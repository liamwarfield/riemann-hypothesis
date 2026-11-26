module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsRecrecLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalFixedPointAtPlace
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
namespace GlobalTheory.PlaceFix
theorem fixed_at_place_of_local_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → FixBase X.core X.R.toRealDat j τ ∧ FixDat (baseOf Z c w j) τ := by
  intro hP D X X0 Y S YS Z c w j H τ hτ
  have hC := X.char
  have hτ' : ∀ z ∈ (embLL0 D).fieldRange, τ z = z := by
    rintro _ ⟨y, rfl⟩
    exact hτ y
  have hTie : TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have hFB : FixBase X.core X.R.toRealDat j τ :=
    GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField _ _ _ _ _ _ hP.rayF X.core X.R X.cG S YS X.F.lv2 X.geo.κ X.geo.v₀ X.geo.fw.laws
      ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ ⟨X.geo.fw⟩ hTie H.field.galois
      H.field.vals H.field.ray H.field.roots j τ hτ'
  refine ⟨hFB, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := de_chi_eq Z.good (c.twI w) j (c.sd w) y
    change τ (((Z.ρ.B _ j _).de.chi y : Circle) : ℂ) = _
    rw [hσ]
    refine GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values Z.ρ Z.good _ j _ (X.R.C.delAt (D.ntw.l (c.twI w))) (Z.pin.delta _ j _) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [H.field.vals.del', H.field.vals.del]
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := (Z.ρ.eG (c.twI w) j (c.sd w)).surjective q
    obtain ⟨g, rfl⟩ := (X.R.eG.trans X.cG).surjective y
    have hU : X.cG (X.R.eG g) ∈ D.nexp.U := ((Z.tie (c.twI w) j (c.sd w)).U_eq _).1 hq
    have hg : g ∈ X.F.P0 := (H.U_eq g).1 hU
    have e1 := (Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hU⟩ hq
    have e2 := H.psi_eq (c.twI w) (c.sd w) ⟨g, hg⟩ hU
    obtain ⟨y, hy⟩ := H.pins.keep.levKs.1 ⟨g, hg⟩
    have e3 := e1.trans e2
    change τ ((((Z.ρ.B _ j _).G.P.chi ⟨_, hq⟩ : ℂˣ) : ℂ)) = _
    have e4 : D.what₂.embLL (X.F.ψ0 ⟨g, hg⟩ : D.what₂.LLˣ) = embLL0 D (S.kKs ((YS.fi j).eK.symm y)) := by
      change _ = D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm y) : ↥D.LL0) : D.what₂.LL)
      rw [S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]
      exact congrArg _ hy.symm
    rw [e4] at e3
    refine (congrArg τ e3).trans (Eq.trans ?_ e3.symm)
    rw [map_inv₀, hτ]
  · exact (GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hC.lev Z.good Z.pin _ j _).fix_mu hC.lev (Z.good.base _ j _) hFB.chi
end GlobalTheory.PlaceFix
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fixed_point_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → FixBase X.core X.R.toRealDat j τ ∧ FixDat (baseOf Z c w j) τ := by
  first | exact @_root_.GlobalTheory.PlaceFix.fixed_at_place_of_local_alt | exact _root_.GlobalTheory.PlaceFix.fixed_at_place_of_local_alt | (intros; apply _root_.GlobalTheory.PlaceFix.fixed_at_place_of_local_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelCharAllSt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelCharAllSt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.StateLevel
theorem level_char_allSt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ _ w _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x, (∀ g : Gc B w.px, x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U ↔ g ∈ x.m.z.F.P0) ∧
  ∀ i b (g : x.m.z.F.P0) (h : x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U), l.b.ser.ex.ρ.e i b ((Dof x).nexp.psiU i b ⟨_, h⟩ : (FractionRing ((Dof x).ntw.O i))ˣ) = ((Dof x).what₂.embLL (x.m.z.F.ψ0 g : (Dof x).what₂.LLˣ))⁻¹ := by
  intro hL
  refine StepW.of_all fun _ _ _ _ _ _ _ _ _ x l => ?_
  have hU : (Dof x).nexp.U = Formalism.IndefR.NX.U (Dof x).nd := l.b.Bs.exp.U_eq
  refine ⟨fun g => ?_, fun i b g h => ?_⟩
  · rw [hU]
    exact (l.rat.rat.lvl g).symm
  · have hu' : (x.m.z.R.eG.trans x.m.z.cG) g ∈ Formalism.IndefR.NX.U (Dof x).nd := hU ▸ h
    have e := l.b.Bs.psiU i b _ h hu'
    have e2 := l.rat.rat.psi g hu'
    have h1 := l.b.ser.ex.good.e_LL0 i b (psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩)
    refine (congrArg (l.b.ser.ex.ρ.e i b) e).trans (h1.trans ?_)
    change (Dof x).what₂.embLL ((psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩ : (↥(Dof x).LL0)ˣ) : (Dof x).what₂.LL) = _
    rw [e2, Units.val_inv_eq_inv_val, map_inv₀]
end GlobalTheory.StateLevel
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelCharAllStStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_character_eq_inv_emb_psi0 : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ _ w _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x, (∀ g : Gc B w.px, x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U ↔ g ∈ x.m.z.F.P0) ∧
  ∀ i b (g : x.m.z.F.P0) (h : x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U), l.b.ser.ex.ρ.e i b ((Dof x).nexp.psiU i b ⟨_, h⟩ : (FractionRing ((Dof x).ntw.O i))ˣ) = ((Dof x).what₂.embLL (x.m.z.F.ψ0 g : (Dof x).what₂.LLˣ))⁻¹ := by
  first | exact @_root_.GlobalTheory.StateLevel.level_char_allSt_alt | exact _root_.GlobalTheory.StateLevel.level_char_allSt_alt | (intros; apply _root_.GlobalTheory.StateLevel.level_char_allSt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalComponentAtPlaceDetermined
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RationalSeriesCoeffAtState
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.PlaceRead.SeriesAtState
theorem rational_series_coeff_at_state_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (i : (Dof x).ntw.Tw), (Dof x).ntw.NonzeroIndexPlace i → ∀ j b, GlobalTheory.SeriesTie.RatRow l.b.YS x.m.z.geo.v₀ l.b.ser.ex.good i j b := by
  intro hP hS hLL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hF : StepW Start fun _ B f T w => ∀ (Z : w.Lt) (X : GlobalTheory.TwInputs.RealSide (w.st Z).toD7), X.R.C = (TC.cf w.I w.l Z) →
      GlobalTheory.TwInputs.FieldOk X :=
    EvG.imp (_root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G hK _ _ w _ Z => (G hK _ w Z).1
  refine (((((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).and hF).and (_root_.GlobalTheory.HeightCounting.Up.sXd_all_alt hLL)).and
    (_root_.GlobalTheory.T.series_character_eq_inv_emb_psi0 hLL)).trans (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := H
  intro P x l
  obtain ⟨hHo, -⟩ := h1 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := h2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := Finite.of_injective _ (ixOf_injective w.I _)
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hX : GlobalTheory.TwInputs.FieldOk X := h3 x.o.Z X x.m.z.lev.C
  obtain ⟨xd, hxd⟩ := h4 P x ⟨l.toLI, l.b.toSeriesState⟩
  obtain ⟨hU, hψ⟩ := h5 P x l
  obtain ⟨f', s1, s2, s3⟩ := GlobalTheory.T.exists_rationalHeckeOperators_adelicReading hP.decay hS.hkTr hS.hkRead (Dof x) X _ l.b.YS
  obtain ⟨H, r1, r2⟩ := GlobalTheory.TwInputs.AtLayer.exists_hecke X _ l.b.YS l.b.ser.ex f' s1 s2 s3 l.b.Bs.cHk l.b.Bs.cHk_del
    (GlobalTheory.TwInputs.AtLayer.hkF_zero_of_sideB l.b.Bs l.rat.In.hL_zero)
  let Y : GlobalTheory.TwInputs.SerSide X (twEOf xd) :=
    { S := _
      YS := l.b.YS
      sup := l.b.ser.sup
      H := H
      reads := r1
      del := r2
      Z := l.b.ser.ex
      U_eq := hU
      psi_eq := hψ
      low := low_of_tiedC l.b.Bs.tw
      Sb := fun i Q hQ => by
        have hA : x.m.z.R.Sb = x.m.z.R.Pg := x.m.z.pins.char.allPl
        obtain ⟨k, hk⟩ := l.b.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true Q
          (by rw [l.b.ser.ex.pin.Pg]; exact hA ▸ hQ)
        exact (Dof x).ntw.placesOver_subset_exceptional i k hk
      B_range := fun i _ j _ b => l.b.Bs.tw.B_range i j b
      hk_emb := fun i j b k P y h1 h2 h => l.b.Bs.hk_emb i j b k P y h1 h2 h.2.2.2 h.2.2.1 h.2.1
      hk_split := fun i _ j _ b k P h => by
        obtain ⟨s, hs⟩ := l.b.Bs.tw.hk_split i j b k P h.2.2.2
        exact hs ▸ Polynomial.Splits.multisetProd fun p hp => by
          obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hp
          exact Polynomial.Splits.X_sub_C a
      off := fun i _ => ⟨fun j hj b => l.b.ser.off i j b fun h => hj (Finset.mem_Icc.2 h), l.b.Bs.hEig_zero i⟩
      all := fun i j hj b a => by
        have := hxd i j b (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
        change a ∈ xd.xd0 i j b
        rw [this]; trivial }
  exact (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hP.decay hP.what₂.art hS.rat hS.int (Dof x) X _ Y hX).1
end GlobalTheory.PlaceRead.SeriesAtState
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratRow_of_levelB2_nonzero_index : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (i : (Dof x).ntw.Tw), (Dof x).ntw.NonzeroIndexPlace i → ∀ j b, GlobalTheory.SeriesTie.RatRow l.b.YS x.m.z.geo.v₀ l.b.ser.ex.good i j b := by
  first | exact @_root_.GlobalTheory.PlaceRead.SeriesAtState.rational_series_coeff_at_state_alt | exact _root_.GlobalTheory.PlaceRead.SeriesAtState.rational_series_coeff_at_state_alt | (intros; apply _root_.GlobalTheory.PlaceRead.SeriesAtState.rational_series_coeff_at_state_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalTupleAtPlace
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
namespace GlobalTheory.PlaceTup
theorem has_local_tuples_at_place_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ' : Twist D Circle, ψ'.Good → ConjChar τ (twVia Z.ρ ι) ψ' →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) (twVia Z.ρ ι) ψ' := by
  intro hDS hCW _ hP D X X0 Y S YS Z c w j H ι hι τ hτ ψ' hψ' hC
  have hC0 := X.char
  have hL : GlobalTheory.BigOn.Exp.TwConj.Laws X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) :=
    ⟨⟨hC0.lev, hC0.grp, hC0.fam, hC0.models, hC0.chain, hC0.thP⟩, X.finT, ⟨X.geo.fw⟩,
      GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC0.lev hC0.fam hC0.models hC0.thP, X.guard, X.geo.pins j,
      by
        convert X.geo.phase j X.unif using 2
        all_goals (rename_i k; rw [X.phs k]; try simp),
      GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hC0.lev Z.good Z.pin (c.twI w) j (c.sd w)⟩
  exact GlobalTheory.T.twist_conjugate_tuples_same_realisation_extension hDS hCW hP.decay hP.what₂.art hP.ray X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j
    (baseOf Z c w j) X.host hL (twVia Z.ρ ι) ψ' (Y.tupT (D.what₂.muTw w)) τ (H.tup ι hι) hC
    (_root_.GlobalTheory.PlaceFix.fixed_at_place_of_local_alt hP D X X0 Y S YS Z c w j H τ hτ).2
end GlobalTheory.PlaceTup
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_tuple_of_discrete_series_read : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ' : Twist D Circle, ψ'.Good → ConjChar τ (twVia Z.ρ ι) ψ' →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) (twVia Z.ρ ι) ψ' := by
  first | exact @_root_.GlobalTheory.PlaceTup.has_local_tuples_at_place_alt | exact _root_.GlobalTheory.PlaceTup.has_local_tuples_at_place_alt | (intros; apply _root_.GlobalTheory.PlaceTup.has_local_tuples_at_place_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalTupleAtState
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
noncomputable section
namespace GlobalTheory.PlaceRead.TupAt
section General
open Formalism.IndefR Formalism.IndefR.Links _root_.Formalism.L2.DIV GlobalTheory.SeriesTie Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {D : D7}
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
end General
section State
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P)
end State
theorem clsQ_at_state_of_choiceSide : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → ∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) (GlobalTheory.PlaceRead.chr ch v) →
  IntegralHeckeForms.ClsQ (D := Dof x) (ch.Q v) ∧ ∀ (j : Fin (Dof x).R.m) (ι : GlobalTheory.PlaceRead.KE ch v →+* ℂ), (∀ y, ι (ch.embW v y) = (Dof x).what₂.embLL y) →
    GlobalTheory.ConjTwist.IsTupOf x.m.z.R.toRealDat (l.b.ser.ex.ρ.B (ch.twI v) j (ch.sd v)) (GlobalTheory.PlaceRead.twVia l.b.ser.ex.ρ ι) (x.r.Y.tupT ((Dof x).what₂.muTw v)) := by
  intro _ hL
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg GlobalTheory.Mem.R3.OkVals.large_coefficientField_contains_twist_values)
  refine s1.trans (Step.of_all ?_)
  intro K B f T _ _ _ hOk w _ P x l ch tp _ hpsi _ _ side v hv hok
  have hV : ValsIn w.I := (hOk w.px w.I P.hX w.ok w.C_eq w.xi_range).1
  clear hOk s1
  have hψ : IsPsi ((Dof x).ntw.l (ch.twI v)) (ch.Q v) (tp.psi v) := by
    have h := tp.psi_is v hv
    rw [← ch.twI_l v] at h
    exact h
  have he : tp.psi v = T.psi v := congrFun hpsi v
  have ht := xi_mu x ch hv he
  have hr := fun PP => ram_mul x.m.z.R.C (ch.twI v) hψ PP
  rw [← ht] at hr
  refine ⟨fun PP hP => ?_, fun j ι hι => ?_⟩
  · obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP fun hu => (hψ.ram PP).1 (he ▸ hu :) hP
    exact splitK_of_prime (D := Dof x) PP h1 fun hd => h2 (Or.inl hd)
  · rw [tupT_muTw x hv]
    refine isTupOf x.m.z.lev.is l.b.ser.ex.good l.b.ser.ex.pin _ j _ hψ ht (fun PP hP => ?_) _ ?_ rfl
    · have hs : IsSplitPl (Dof x).host PP := by
        rcases (hr PP).1 ((x.m.z.lev.is.Q_ram _ PP).2 (Or.inl hP)) with h | h
        · obtain ⟨q, -, hq, e⟩ := isDelta_delAt x.m.z.R.C (ch.twI v)
          have h' := (hq PP).1 h
          refine l.a.elem.split PP (e.imp (fun e => ?_) fun e => ?_) <;> subst e <;> exact h'
        · exact hψ.split PP h
      refine (l.b.ser.ch _ PP hs).2 ?_
      obtain ⟨u, -, e⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 ((x.m.z.lev.Q _).le hP)
      exact l.sel.ge ⟨u, e⟩
    · refine chrEq_twVia side.psi hv hok l.b.ser.ex.good (fun PP h1 h2 => ?_) ι hι
      have hval : ValLL0 (Dof x) x.m.z.R.C := by rw [x.m.z.lev.C]; exact l.a.val
      obtain ⟨y, hy⟩ := val_delAt hval _ PP h2
      have hx := x.m.z.lev.xiH (x.m.z.R.mu ((Dof x).plEq v))
      obtain ⟨z, hz⟩ := hV.1 _ PP (hx ▸ not_not.1 fun hu => ((hr PP).1 hu).elim h2 h1 :)
      have hz' : (Dof x).what₂.embLL z = (((x.m.z.R.C.delAt ((Dof x).ntw.l (ch.twI v)) * tp.psi v).val PP : ℂˣ) : ℂ) :=
        hz.trans (congrArg (fun χ : HChar (Dof x).host.E => ((χ.val PP : ℂˣ) : ℂ)) (hx.symm.trans ht))
      refine ⟨y⁻¹ * (show (Dof x).what₂.LL from z), ?_⟩
      rw [map_mul, map_inv₀, hy]
      refine (congrArg _ hz').trans ?_
      rw [HChar.val_mul, Units.val_mul, inv_mul_cancel_left₀ (Units.ne_zero _)]
end GlobalTheory.PlaceRead.TupAt
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clsQ_of_choiceSide_twOK_at_state : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → ∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) (GlobalTheory.PlaceRead.chr ch v) →
  IntegralHeckeForms.ClsQ (D := Dof x) (ch.Q v) ∧ ∀ (j : Fin (Dof x).R.m) (ι : GlobalTheory.PlaceRead.KE ch v →+* ℂ), (∀ y, ι (ch.embW v y) = (Dof x).what₂.embLL y) →
    GlobalTheory.ConjTwist.IsTupOf x.m.z.R.toRealDat (l.b.ser.ex.ρ.B (ch.twI v) j (ch.sd v)) (GlobalTheory.PlaceRead.twVia l.b.ser.ex.ρ ι) (x.r.Y.tupT ((Dof x).what₂.muTw v)) := by
  first | exact @_root_.GlobalTheory.PlaceRead.TupAt.clsQ_at_state_of_choiceSide | exact _root_.GlobalTheory.PlaceRead.TupAt.clsQ_at_state_of_choiceSide | (intros; apply _root_.GlobalTheory.PlaceRead.TupAt.clsQ_at_state_of_choiceSide <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalConjExpansionAtPlace
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.HeightCounting.Up (PrN)
theorem GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ (ζ : ℂ) (Φ Φ' : GA D (Wc D j) → ℂ), ConjFun (X.geo.O j) (X.geo.κ j) τ ζ Φ Φ' →
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → NX.FmK S (j.1 + 1)), Φ = ∑ k, a k • evW YS X.geo.v₀ j (f k).val → Φ' = ζ • ∑ k, τ (a k) • evW YS X.geo.v₀ j (f k).val := by
  intro _ D X X0 Y S YS Z c w j _ τ _ ζ Φ Φ' hC n a f hΦ
  have hb := GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls.base_of_tie (i := j) X.geo.fw
  have hso : (X.geo.O j).s0 = res X.core (sg0 _ X.A3.A) :=
    (sOv_eq X.core.toCore (X.geo.O j).c' (X.geo.O j).hle).trans hb.1.symm
  have hev := GlobalTheory.PlaceRead.evaluates_of_lunif X.geo.fw X.unif j (sg0 _ X.A3.A) hb.2.1 hb.2.2
  let cf : NX.FmK S ((j : ℕ) + 1) → X.core.cuspA ((j : ℕ) + 1) (wtA (X.geo.κ j)) (X.geo.κ j).n := fun g =>
    (X.geo.fw.e j).symm ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩
  have hread : ∀ (g : NX.FmK S ((j : ℕ) + 1)) h,
      (lieFac (X.core.Q.Dw ((j : ℕ) + 1)) (xiR D) (wtA (X.geo.κ j)) : ℂ) *
      (X.geo.O j).phi (X.core.cE ((j : ℕ) + 1) (X.geo.O j).s0) (cf g : X.core.R ((j : ℕ) + 1)) h =
        evW YS X.geo.v₀ j g.val h := by
    intro g h
    rw [phi_cE X.core X.R.toRealDat X.geo.O j]
    refine Eq.trans ?_ ((congrFun (hev (cf g)) h).symm.trans ?_)
    · exact congrFun (GlobalTheory.LiftRatObj.phiC_congr X.core hso (X.geo.O j).hV hb.2.2 _ _) h
    · have he : X.geo.fw.e j (cf g) = ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩ := LinearEquiv.apply_symm_apply _ _
      exact congrArg (fun x : (X.R.FW j).WK => (X.R.HW j (sg0 D X.A3.A)).e ((X.R.FW j).j (sg0 D X.A3.A) x.val)
        (X.geo.v₀ j (sg0 D X.A3.A)) h) he
  have h1 : Expands (X.geo.O j) (X.geo.κ j) Φ a fun k => cf (f k) := fun h => by
    rw [hΦ, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (hread _ _).symm
  have h2 := hC.2 n a _ h1
  funext h
  rw [h2 h, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact (congrArg (fun z => ζ * τ (a k) * z) (hread (f k) h)).trans (mul_assoc _ _ _)
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_conj_expansion_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ (ζ : ℂ) (Φ Φ' : GA D (Wc D j) → ℂ), ConjFun (X.geo.O j) (X.geo.κ j) τ ζ Φ Φ' →
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → NX.FmK S (j.1 + 1)), Φ = ∑ k, a k • evW YS X.geo.v₀ j (f k).val → Φ' = ζ • ∑ k, τ (a k) • evW YS X.geo.v₀ j (f k).val := by
  first | exact @_root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer | exact _root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer | (intros; apply _root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.HeightCounting.Up (PrN)
namespace GlobalTheory.PlaceRead
variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}
variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}
end GlobalTheory.PlaceRead
namespace GlobalTheory.PlaceRead
variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} {Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0} {S : NX.RatDat D.ntw}
  {YS : NX.NExpRealS X.R X.cG S} {Z : ExportTie YS X.geo.v₀} {c : NChoice D} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem exists_local_component_at_place_alt (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (H : AtPlace Y Z c w j) {ε : KE c w →+* ℂ} (hε : Extends Z.ρ ε) :
    ∃ (Ψ : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[ε.comp (c.embW w)] Amb D j) (N : ℕ) (z₁ : ℂ),
      (∀ (I : Type) (b : I → D.what₂.MtL (D.what₂.muTw w) (j.1 + 1)),
        LinearIndependent ℂ (fun k => D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (b k)) → LinearIndependent ℂ fun k => Ψ (b k)) ∧
      ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia Z.ρ ε) : Set (Amb D j)) =
        Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)) ∧
      IsUnit (N : c.Oe w) ∧ UnitOff N z₁ ∧
      ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
        (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
          Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
        (baseOf Z c w j).classSum (Z.ρ.om (c.twI w) j (c.sd w) (twVia Z.ρ ε).chi) (twVia Z.ρ ε)
          (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) (Ψ x) =
          z₁ • (Z.ν (c.twI w) j (c.sd w))⁻¹ • ∑ k, ε (c.embW w (a k)) • evW YS X.geo.v₀ j (f k).val := by
  obtain ⟨τ, hτ0⟩ := GlobalTheory.BigOn.Exp.TwConj.exists_aut_on D.what₂.embLL (ε.comp (c.embW w))
    (GlobalTheory.BigOn.Exp.TwConj.countable_alg D.what₂.embLL)
  have hτ : ∀ x, τ (D.what₂.embLL x) = ε (c.embW w x) := fun x =>
    hτ0 x ((Algebra.IsAlgebraic.isAlgebraic x).algHom D.what₂.embLL.toRatAlgHom)
  have hfix : ∀ a, τ (embLL0 D a) = embLL0 D a := fun a => (hτ a).trans (H.emb ε hε a)
  obtain ⟨ι, hιε⟩ : ∃ ι : KE c w →+* ℂ, (τ : ℂ →+* ℂ).comp ι = ε :=
    ⟨(τ.symm : ℂ →+* ℂ).comp ε, RingHom.ext fun y => τ.apply_symm_apply _⟩
  have hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x := fun x => τ.injective ((RingHom.congr_fun hιε _).trans (hτ x).symm)
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo : BaseOf X.R.toRealDat j (baseOf Z c w j) :=
    GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  obtain ⟨hg, ha, hcc⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ι
  obtain ⟨hg', ha', -⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ε
  have hcj : ConjChar τ (twVia Z.ρ ι) (twVia Z.ρ ε) := hιε ▸ hcc τ
  obtain ⟨u, cc, κ, hu, hc, hκ, hval, hfn, hs, hν⟩ := GlobalTheory.T.exists_scale_twisted_place_coefficient_map D X X0 Y S YS Z c w j H
  obtain ⟨hfb, hfd⟩ := _root_.GlobalTheory.T.local_fixed_point_of_third_layer hP D X X0 Y S YS Z c w j H τ hfix
  obtain ⟨C, hC1, hC2⟩ := GlobalTheory.T.conjugation_scaled_coords_integral_forms_twist D j _ hB hBo.lam (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ hκ hval hfn τ hfix _ _ hg hg' hcj hfd
  have hω := Z.good.weil (c.twI w) j (c.sd w) _ hg
  have hω' := Z.good.weil (c.twI w) j (c.sd w) _ hg'
  have hcl' := Z.good.classes (c.twI w) j (c.sd w) _ hg' ha'
  have hcl : IsClassSystem (Vc D j) ((baseOf Z c w j).levJ (twVia Z.ρ ι)) (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) := by
    rw [← levJ_congr (baseOf Z c w j) hcj.1]
    exact hcl'
  refine (GlobalTheory.T.thetaLift_twistLevelForm_eq_unit_mul_classSum D X j _ hB hBo _ _ hg ha (H.tup ι hι) _ hω _ _ hcl u).elim fun z hz => hz.elim fun a₀ hz => ?_
  obtain ⟨hz, ha₀, hth⟩ := hz
  refine (GlobalTheory.T.classSums_conjugate_twists_conjugate_expansions D X j _ hB _ _ hg hg' ha (_root_.GlobalTheory.T.exists_local_tuple_of_discrete_series_read hCo hCW hHM hP D X X0 Y S YS Z c w j H ι hι τ hfix _ hg' hcj) u cc κ hu hc hκ τ hfb hfd
    hcj _ _ hω hω').elim fun ζ hζ => ?_
  obtain ⟨hζ, hcs⟩ := hζ
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u hu
  have hmem : ∀ y, fockOf Y (used_of_tw H.tw) j u y ∈ (baseOf Z c w j).formsC (twVia Z.ρ ι) := fun y =>
    hrange.le (LinearMap.mem_range_self _ y)
  have hΦv : ∀ y h, trOf H u κ z y h ∈ (baseOf Z c w j).valSpace := fun y h =>
    Submodule.smul_mem _ κ⁻¹ (((baseOf Z c w j).mem_formsC.1 (hmem y)).1 _)
  have hN := (GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple D X X0 Y S YS Z c w j H ι hι).2.2
  refine ⟨semiComp τ (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1)) (trOf H u κ z) C (ε.comp (c.embW w)) hτ, _, _, fun I b hb => ?_, ?_, hN, unitOff_conj τ ha₀ hζ hν, fun x hx n a f hf => ?_⟩
  · exact indep_conj τ (trOf H u κ z) C (fun y hy => trOf_eq_zero H hκ hinj y ((hC1 _ (hΦv y)).2 hy)) hb
  · have e1 : (ringOf ι).map (τ : ℂ →+* ℂ) = ringOf ε := by
      rw [← hιε, ringOf, ringOf, RingHom.map_range, RingHom.comp_assoc]
    have e2 := hC2 _ (coefficient_ring_of_integral_le (intLL_le hι))
    rw [e1] at e2
    exact span_conj H hι hιε hu hκ hs hz C _ e2
  · have h1 := expansion_eq H hu hκ ha₀.1 _ hx (hth _ (hmem (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) hf
    have h2 := _root_.GlobalTheory.T.local_conj_expansion_of_third_layer hP D X X0 Y S YS Z c w j H τ hfix ζ _ _
      (hcs _ _ hcl'.fin _ _ (hC1 _ (hΦv (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))).1) n _ f h1
    exact rescale_conj τ hκ (Z.scalar (c.twI w) j (c.sd w)).ne (fun k => hτ (a k)) h2
theorem exists_basisAt_latAt_thetaAt_of_atPlace (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (H : AtPlace Y Z c w j) :
    ∃ (e : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[c.embW w] Tgt c w (j.1 + 1)) (u : (FractionRing (c.Oe w))ˣ),
      BasisAt c w (j.1 + 1) e ∧ LatAt c w (j.1 + 1) e (u : FractionRing (c.Oe w)) ∧ ThetaAt Y YS c w j e (u : FractionRing (c.Oe w)) := by
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField D c w Z.ρ Z.good).1
  refine (_root_.GlobalTheory.PlaceRead.exists_local_component_at_place_alt hCo hCW hHM hP H hε).elim fun Ψ h => h.elim fun N h => h.elim fun z₁ h => ?_
  obtain ⟨hind, hlat, hN, hz, hth⟩ := h
  obtain ⟨hinj, hmt⟩ := GlobalTheory.T.definiteFormReading_injective_lattice_integralForms D c w Z.ρ Z.good j _ (Z.tie (c.twI w) j (c.sd w)) ε hε H.ok H.field.roots
  have hsub : ∀ F ∈ Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)), ∃ y ∈ latT c w (j.1 + 1),
      rdE (Z.tie (c.twI w) j (c.sd w)) hε y = F := fun F hF => (hmt F).1 (hlat.ge hF)
  obtain ⟨e, he⟩ := exists_lift (c.embW w) ε _ hinj Ψ (GlobalTheory.T.rationalLatticeTwistedTuple_span_top D w (j.1 + 1)) fun x hx =>
    (hsub _ (Submodule.subset_span ⟨x, hx, rfl⟩)).imp fun _ h => h.2
  have hL : Submodule.span (c.Oe w) (e '' latS w (j.1 + 1)) = latT c w (j.1 + 1) := by
    have h1 := image_span (ε.comp (algebraMap (c.Oe w) (KE c w))) (ringOf ε) rfl
      (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom
      (fun r v => (congrArg _ (algebraMap_smul (KE c w) r v).symm).trans ((rdE (Z.tie (c.twI w) j (c.sd w)) hε).map_smulₛₗ _ v)) (e '' latS w (j.1 + 1))
    have h2 : (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom '' (e '' latS w (j.1 + 1)) = Ψ '' latS w (j.1 + 1) := by
      rw [Set.image_image]
      exact Set.image_congr fun x _ => he x
    rw [h2] at h1
    refine le_antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨y', hy', e1⟩ := hsub _ (h1.le ⟨y, hy, rfl⟩)
      exact hinj e1 ▸ hy'
    · obtain ⟨y', hy', e1⟩ := h1.ge (hlat.le ((hmt _).2 ⟨y, hy, rfl⟩))
      exact hinj e1 ▸ hy'
  have hb : BasisAt c w (j.1 + 1) e := fun b => by
    refine ⟨indep_of_read ε (rdE (Z.tie (c.twI w) j (c.sd w)) hε) ?_, top_unique ?_⟩
    · simp only [he]
      exact hind _ b (D.what₂.jMt_basis _ _ b).1
    · rw [← span_latT, ← hL]
      refine Submodule.span_le.2 fun y hy => ?_
      refine (Submodule.span_le (p := (Submodule.span (KE c w) (Set.range fun i => e (b i))).restrictScalars (c.Oe w))).2 ?_ hy
      rintro _ ⟨x, -, rfl⟩
      exact mem_span_basis e b x
  have hfa : Faithful (Z.rd (c.twI w) j (c.sd w)) :=
    GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ X.R X.cG S YS X.geo.v₀ Z.ρ Z.good _ j _ _ (Z.scalar _ j _).ne X.unif
      X.char.models.HW (Z.vec j) H.ks
  have hrat := GlobalTheory.T.class_sums_twisted_definite_forms_rational D Z.ρ Z.good _ j _ _ (Z.tie (c.twI w) j (c.sd w)) (Z.rat H.rat).2.1 H.field.roots _ _ _ H.ok H.cls
  have key : ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
      (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
        Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
      rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (NChoice.thPe D c w (j.1 + 1) (e x)) =
        z₁ • rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
          (YS.eF (c.twI w) (j.1 + 1) (c.sd w) (Nat.le_add_left _ _) j.2).symm ((1 : NX.KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)) := by
    intro x hx n a f hf
    have h1 := hth x hx n a f hf
    rw [hε.twVia_eq] at h1
    refine (rdF_thPe _ hε H.ok hrat _).trans ((congrArg _ (he x)).trans (h1.trans (congrArg (z₁ • ·) ?_)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rdF_tmul, smul_comm]
    refine congrArg (ε (c.embW w (a k)) • ·) ?_
    refine Eq.trans ?_ (realRd_tmul YS X.geo.v₀ Z.good (c.twI w) j (c.sd w) _ 1 (f k)).symm
    rw [show Z.ρ.e (c.twI w) (c.sd w) (1 : NX.KB S (c.twI w) (c.sd w)) = 1 from map_one _, mul_one]
  have hco := fun x hx n a f hf => GlobalTheory.T.chosenField_forms_proportional_of_readings D c w Z.ρ Z.good j _ hfa ε hε _ _ z₁ (key x hx n a f hf)
  obtain ⟨o, ho⟩ : ∃ o : (c.Oe w)ˣ, ThetaAt Y YS c w j e (algebraMap (c.Oe w) (KE c w) o) := by
    by_cases hex : ∃ t : KE c w, ε t = z₁
    · obtain ⟨t, ht⟩ := hex
      obtain ⟨o, rfl⟩ := GlobalTheory.T.exists_integral_unit_of_isUnitAwayFromLevel_embedding (c.Oe w) ε N t hN (ht ▸ hz)
      refine ⟨o, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', e1⟩ := h1 hB
      exact e1.trans (congrArg (· • _) (ε.injective (ht'.trans ht.symm)))
    · refine ⟨1, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', -⟩ := h1 hB
      exact absurd ⟨t', ht'⟩ hex
  exact ⟨e, Units.map (algebraMap (c.Oe w) (KE c w)).toMonoidHom o, hb, hL.trans (span_smul_latT _ o).symm, ho⟩
end GlobalTheory.PlaceRead
namespace GlobalTheory.PlaceRead
open Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem exists_local_map_at_place_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∀ v, TwistedAt (Dof x) v → ∀ i : Fin (Dof x).R.m, ∃ (e : (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1)) (u : (FractionRing (ch.Oe v))ˣ), GlobalTheory.ChoiceRead.BasisAt ch v (i.1 + 1) e ∧ GlobalTheory.ChoiceRead.LatAt ch v (i.1 + 1) e (u : FractionRing (ch.Oe v)) ∧ GlobalTheory.ChoiceRead.ThetaAt x.r.Y l.b.YS ch v i e (u : FractionRing (ch.Oe v)) := by
  intro hCo hCW hHM hP hS hL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hF : StepW Start fun _ _ _ _ w => ∀ (Z : w.Lt) (X : RealSide (w.st Z).toD7), X.R.C = TC.cf w.I w.l Z → FieldOk X :=
    EvG.imp (_root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP) fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp _ _ w _ Z => (H kp T w Z).1
  refine (((((_root_.GlobalTheory.T.ratRow_of_levelB2_nonzero_index hP hS hL).and (_root_.GlobalTheory.T.clsQ_of_choiceSide_twOK_at_state hP hL)).and (_root_.GlobalTheory.T.series_character_eq_inv_emb_psi0 hL)).and hF).and
    ((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev))).trans
    (StepW.of_all fun K B f T w hO _ H P x => ?_)
  intro l ch tp hxi hpsi hQ hk hside hok v hv i
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := H
  obtain ⟨hHo, -⟩ := h5 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := h6 (w.st x.o.Z) hO
  let X := RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo (Finite.of_injective _ (ixOf_injective w.I _)) hHo hStd hSize
  have hf : FieldOk X := h4 x.o.Z X x.m.z.lev.C
  obtain ⟨k1, k2⟩ := h2 P x l ch tp hxi hpsi hQ hk hside v hv (hok v hv)
  obtain ⟨k3, k4⟩ := h3 P x l
  obtain ⟨ψ0, -, k5, -⟩ := hside.nct.psi_eq
  exact _root_.GlobalTheory.PlaceRead.exists_basisAt_latAt_thetaAt_of_atPlace (X := X) (Y := x.r.Y) (YS := l.b.YS) (Z := l.b.ser.ex) hCo hCW hHM hP
    { pins := x.m.z.pins, intersectionNumber_baseChange := x.m.intersectionNumber_baseChange, field := hf, tw := hv, ok := hok v hv, cls := k1
      emb := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField _ ch v _ l.b.ser.ex.good).2 hside.nct
      val := fun σ => ⟨_, (k5 v σ).trans (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
      U_eq := k3, psi_eq := k4, ks := l.rat.In.ks _ (Nat.le_add_left _ _) i.2
      rat := h1 P x l _ (GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ ch hside.nct hf.galois v hv) i _
      tup := k2 i }
end GlobalTheory.PlaceRead
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_at_place_determined_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∀ v, TwistedAt (Dof x) v → ∀ i : Fin (Dof x).R.m, ∃ (e : (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1)) (u : (FractionRing (ch.Oe v))ˣ), GlobalTheory.ChoiceRead.BasisAt ch v (i.1 + 1) e ∧ GlobalTheory.ChoiceRead.LatAt ch v (i.1 + 1) e (u : FractionRing (ch.Oe v)) ∧ GlobalTheory.ChoiceRead.ThetaAt x.r.Y l.b.YS ch v i e (u : FractionRing (ch.Oe v)) := by
  first | exact @_root_.GlobalTheory.PlaceRead.exists_local_map_at_place_alt | exact _root_.GlobalTheory.PlaceRead.exists_local_map_at_place_alt | (intros; apply _root_.GlobalTheory.PlaceRead.exists_local_map_at_place_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
theorem GlobalTheory.ChoiceRead.exists_stC_choice_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi, c.ch.twI = ch.twI := by
  intro hCo hCW hHM hPr hSer hL
  refine (_root_.GlobalTheory.T.local_component_at_place_determined_alt hCo hCW hHM hPr hSer hL).trans (StepW.of_all fun K B f T w _ _ H P x => ?_)
  intro l ch tp hxi hpsi hQ hk hside hok
  have hc := H P x l ch tp hxi hpsi hQ hk hside hok
  choose e u hb hl hth using hc
  let G : ∀ v, (Dof x).what₂.muAt v ≠ (Dof x).what₂.mu0 → ∀ i : Fin (Dof x).R.m,
      (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1) :=
    fun v hv i => (((u v hv i)⁻¹ : (FractionRing (ch.Oe v))ˣ) : FractionRing (ch.Oe v)) • e v hv i
  have HB := GlobalTheory.ChoiceRead.pick_prop ch G (fun v j E => GlobalTheory.ChoiceRead.BasisAt ch v j E)
    (fun v hv i => (hb v hv i).smul _)
  have HL := GlobalTheory.ChoiceRead.pick_prop ch G
    (fun v j E => Submodule.span (ch.Oe v) (E '' GlobalTheory.ChoiceRead.latS v j) = GlobalTheory.ChoiceRead.latT ch v j)
    (fun v hv i => GlobalTheory.ChoiceRead.LatAt.smul_inv _ (hl v hv i))
  refine ⟨⟨GlobalTheory.ChoiceRead.withE ch (GlobalTheory.ChoiceRead.pick ch G) HB HL, GlobalTheory.ChoiceRead.tupWithE tp _ HB HL, hxi, hpsi, hQ, hk,
    GlobalTheory.ChoiceRead.choiceSide_withE hside _ HB HL, hok, ?_⟩, rfl⟩
  refine GlobalTheory.ChoiceRead.emtTheta_withE _ HB HL fun v i hv => ?_
  rw [GlobalTheory.ChoiceRead.pick_eq ch G v hv i]
  exact (hth v hv i).smul_inv _
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGalois_exists_choice_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi, c.ch.twI = ch.twI := by
  first | exact @_root_.GlobalTheory.ChoiceRead.exists_stC_choice_alt | exact _root_.GlobalTheory.ChoiceRead.exists_stC_choice_alt | (intros; apply _root_.GlobalTheory.ChoiceRead.exists_stC_choice_alt <;> assumption)
end
end
