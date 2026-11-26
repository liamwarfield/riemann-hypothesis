module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalPairActsOnVacuaByHeisenbergComb

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLatticeVacuumMemSpanInertTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLatticeVacuumMemSpanInertTranslates
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem secW_compFin (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (a : AE D)
    (ha : algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) * a = a) :
    secW hw h (GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a)) = a := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm
    (GlobalTheory.LFun.InertChart.complEquiv hw h _)) = a
  rw [RingEquiv.symm_apply_apply]
  conv_rhs => rw [← ha]
  rw [show algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) = GlobalTheory.EmbChart.tensAt D.host.E v 1 from rfl,
    GlobalTheory.EmbChart.tensAt_mul_right, one_mul]

theorem exists_uPt_eq (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {k : w.adicCompletion D.host.E} (hk0 : k ≠ 0) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E))
    (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) {u : WO S T}
    (hu : IsHalf (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v)) u) :
    ∃ y, uPt hw h k aS aT y = u := by
  let U : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) :=
    u.map fun a => GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a)
  refine ⟨k⁻¹ • ((aT⁻¹).1 * U * aS.1), ?_⟩
  have e1 : k • (aT.1 * (k⁻¹ • ((aT⁻¹).1 * U * aS.1)) * (aS⁻¹).1) = U := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hk0, one_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext i j
  rw [uPt, e1, Matrix.map_apply]
  exact secW_compFin hw h _ (hu i j)


open GlobalTheory.Hk3 GlobalTheory.InertLoc GlobalTheory.SplitScalar GlobalTheory.FinWeilO in
set_option maxHeartbeats 1600000 in
theorem om_mem_span_uPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v), UnrAt χS w → UnrAt χT w → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsUnramInv ϖ c (qV D.host.F v) → IsConjAt D.sp.cm.sig h c → GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ f, VacFin ψ S T v f → ∀ (gS : Gv S v) (gT : Gv T v), om (embV S v gS, embV T v gT) f ∈ Submodule.span ℂ (Set.range fun x => heisO ψ S T (uPt hw h k aS aT x) f) := by
  intro D ψ S T χS χT om hW v w hw h uS uT c ϖ k aS aT hU hconj hk haS haT gaS gaT f hf gS gT
  have dict := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have hP : Formalism.DivisionValues.conjPl w = w := by
    by_contra hne
    exact GlobalTheory.LFun.not_isSplit_of_isInertAt hw (dict.1.2 hne)
  have he : IsPrimeIdem w (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v))
      (algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v)) :=
    GlobalTheory.HeckeRowsCompare.isPrimeIdem_of_inert hw (GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D v)
  set e := algebraMap (AF D.host.F) (AE D) (GlobalTheory.AdelicU.Supp.placeIdem v) with he_def
  have unr : ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → GlobalTheory.Hk3.UnrPl w χ := fun χ hχ =>
    dict.2.1 χ fun w' hw' => by rw [(GlobalTheory.LFun.InertChart.under_eq_iff hw w').1 hw']; exact hχ
  have hfix := GlobalTheory.ConjVacFix.vacFix_of_unrPl ψ S T χS χT om w hW (unr χS uS) (unr χT uT)
  obtain ⟨ϖ0, σ, q, π, hU0, h2, hc0, hV⟩ := exists_chart hP he
  obtain ⟨βS, ιS, hS, gS'⟩ := hV S
  obtain ⟨βT, ιT, hT, gT'⟩ := hV T
  have hψ := hW.std
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := exists_delta_psi hU0 h2 (th ψ hc0 k) (th_conj hc0 hU0.1) (by
    obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
    refine th_cond hψ hc0 hU0.2.1 hβ ⟨0, ?_⟩ hk
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Ranks.rankX', Ranks.r]
    omega)
  let ρ : Matrix (Fin T.rank) (Fin S.rank) (LP D w) → Module.End ℂ (thetaSub ψ S T) := fun x =>
    (heisL ψ S T (kap hc0 βS βT k x)).restrict fun _ hf =>
      GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (hc0.half_fin (kap_half hc0 x)) hf
  have hρ : ∀ x (m : thetaSub ψ S T), (ρ x m : WO S T → ℂ) = heisO ψ S T (kap hc0 βS βT k x) m := fun _ _ => rfl
  let ω : Formalism.UG.UJ σ (1 : Matrix (Fin S.rank) (Fin S.rank) (LP D w)) ×
      Formalism.UG.UJ σ (1 : Matrix (Fin T.rank) (Fin T.rank) (LP D w)) →* Module.End ℂ (thetaSub ψ S T) :=
    { toFun := fun p => (om (ιS p.1, ιT p.2)).restrict fun _ hf => hW.om_pres _ _ hf
      map_one' := LinearMap.ext fun m => Subtype.ext (by
        show om (ιS 1, ιT 1) m = m
        rw [map_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply])
      map_mul' := fun p p' => LinearMap.ext fun m => Subtype.ext (by
        show om (ιS (p.1 * p'.1), ιT (p.2 * p'.2)) m = om (ιS p.1, ιT p.2) (om (ιS p'.1, ιT p'.2) m)
        rw [map_mul, map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]) }
  have hω : ∀ g g' (m : thetaSub ψ S T), (ω (g, g') m : WO S T → ℂ) = om (ιS g, ιT g') m := fun _ _ _ => rfl
  have hlat := kap_mem_iff hc0 hU0.2.1 hS hT hk
  have hvac0 : ∀ m : thetaSub ψ S T, LocVac ρ m ↔
      ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u → heisO ψ S T u m = m := fun m => by
    refine ⟨fun hm u hu hh => ?_, fun hm x hx => Subtype.ext (hm _ ((hlat x).2 hx) (kap_half hc0 x))⟩
    obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
    exact congrArg Subtype.val (hm x ((hlat x).1 hu))
  have hvac : ∀ m : thetaSub ψ S T, LocVac ρ m ↔ IsVacAt ψ S T w m := fun m => by
    rw [hvac0]
    refine ⟨fun hm => ⟨m.2, fun e' f' he' u hu hh => hm u hu ?_⟩, fun hm u hu hh => hm.2 e e he u hu (Or.inl hh)⟩
    obtain ⟨rfl, -⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 w e e he).2.2.2.1 e' f' he'
    rwa [hc0.1.2.1, or_self] at hh
  have hhyp : ∀ {V : HSp D} {β ι}, GrpChart V e σ π β ι → ∀ g, ι g ∈ hyp V w ↔
      g.1 ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.intL (LP D w)) := fun hι g =>
    ⟨fun hg => (hι.2.2.2 g).1 hg.1, fun hg => ⟨(hι.2.2.2 g).2 hg, e, e, he, hι.1 g⟩⟩
  have hone : ∀ (n : ℕ) (i j : Fin n), σ ((1 : Matrix (Fin n) (Fin n) (LP D w)) i j) = (1 : Matrix (Fin n) (Fin n) (LP D w)) j i :=
    fun n i j => by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm, σ.map_one]
      · rw [if_neg hij, if_neg (Ne.symm hij), σ.map_zero]
  have hLP : LocPair ϖ0 σ q δ (1 : GL (Fin S.rank) (LP D w)) (1 : GL (Fin T.rank) (LP D w)) ψ' ρ ω := by
    refine ⟨hU0, odd_of_v_two hU0 h2, one_mem _, one_mem _, hone _, hone _, hδ, p1, p2, ?_, fun x y => ?_, ?_,
      fun g g' x => ?_, fun g g' hg hg' s hs => ?_⟩
    · refine LinearMap.ext fun m => Subtype.ext ?_
      rw [hρ, kap_zero, heisO_zero, Module.End.one_apply]
    · refine LinearMap.ext fun m => Subtype.ext ?_
      rw [Module.End.mul_apply, hρ, hρ, heisO_heisO, symplOH_kap hc0 hS hT, LinearMap.smul_apply, Submodule.coe_smul, hρ,
        kap_add, locH, p3, inv_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
      rfl
    · refine span_vacua hψ hc0.1.1 hc0.1.2.1 (fun u hu hh => ?_) _ fun u hh s m hs hm => ?_
      · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
        refine ⟨kap hc0 βS βT k ((2⁻¹ : LP D w) • x), (hlat _).2 fun i j => mul_mem (mem_intL.2 ?_) ((hlat x).1 hu i j), ?_⟩
        · rw [map_inv₀, h2, inv_one]
        · rw [← kap_add, half_add_half]
      · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) hc0 hk.1 hh
        exact Submodule.subset_span ⟨x, s, (hvac0 s).2 hs, Subtype.ext hm⟩
    · refine LinearMap.ext fun m => Subtype.ext ?_
      show om (ιS g, ιT g') (heisO ψ S T (kap hc0 βS βT k x) m) = heisO ψ S T (kap hc0 βS βT k _) (om (ιS g, ιT g') m)
      rw [hW.om_heis _ _ _ _ m.2, actO_kap hc0 gS' gT']
    · exact Subtype.ext (hfix _ ((hvac s).1 hs) _ ((hhyp gS' g).2 hg) _ ((hhyp gT' g').2 hg'))
  obtain ⟨r1, hr1⟩ := gS'.2.2.1 (embV S v gS) ((GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem S he h _).2 ⟨gS, rfl⟩)
  obtain ⟨r2, hr2⟩ := gT'.2.2.1 (embV T v gT) ((GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem T he h _).2 ⟨gT, rfl⟩)
  let fM : thetaSub ψ S T := ⟨f, hf.1⟩
  have hvf : LocVac ρ fM := (hvac fM).2 (dict.2.2.2.1 ψ S T f hf)
  haveI : CharZero (LP D w) := algebraRat.charZero _
  obtain ⟨cc, hcc⟩ := locPair_act_vac_comb (LP D w) ϖ0 σ q δ S.rank T.rank 1 1 ψ' (thetaSub ψ S T) ρ ω hLP (r1, r2)
  have e1 : om (embV S v gS, embV T v gT) f = ((ω (r1, r2) fM : thetaSub ψ S T) : WO S T → ℂ) := by
    rw [hω, hr1, hr2]
  rw [e1, hcc fM hvf, Finsupp.sum, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [Submodule.coe_smul, hρ]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨y, hy⟩ := exists_uPt_eq hw h hk.1 aS aT (kap_half hc0 x)
  rw [← hy]
  exact Submodule.subset_span ⟨y, rfl⟩

end GlobalTheory.InertFrameLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLatticeVacuumMemSpanInertTranslatesStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_latticeVacuum_mem_span_inertTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v), UnrAt χS w → UnrAt χT w → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsUnramInv ϖ c (qV D.host.F v) → IsConjAt D.sp.cm.sig h c → GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ f, VacFin ψ S T v f → ∀ (gS : Gv S v) (gT : Gv T v), om (embV S v gS, embV T v gT) f ∈ Submodule.span ℂ (Set.range fun x => heisO ψ S T (uPt hw h k aS aT x) f) := by
  first | exact @GlobalTheory.InertFrameLoc.om_mem_span_uPt | exact GlobalTheory.InertFrameLoc.om_mem_span_uPt | (intros; apply GlobalTheory.InertFrameLoc.om_mem_span_uPt <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuedTwoEqOneInertPlaceCmField
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuedTwoEqOneInertPlaceCmField
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertTwo

theorem valued_two_eq_one : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
  intro D v w hi
  have hu : w.under (𝓞 D.host.F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hi w).2 rfl
  have hc : Formalism.DivisionValues.conjPl w = w := GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hi hu
  have h : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h2 => GlobalTheory.CoreThree.conj_ne_of_two w h2 hc
  rw [← map_ofNat (algebraMap D.host.E (w.adicCompletion D.host.E)) 2, GlobalTheory.Idele.valued_algebraMap,
    ← map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 h

end GlobalTheory.InertTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuedTwoEqOneInertPlaceCmFieldStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_two_eq_one_inertPlace_cmField : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
  first | exact @GlobalTheory.InertTwo.valued_two_eq_one | exact GlobalTheory.InertTwo.valued_two_eq_one | (intros; apply GlobalTheory.InertTwo.valued_two_eq_one <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertSupportedPointIntegralFramesMemLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertSupportedPointIntegralFramesMemLattice
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem secW_toCompl_tmul_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (b : Fv D.host.F v) (o m : D.host.E) :
    secW hw h (toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m) =
      pairA D.host.F 0 (singleFin v b) ⊗ₜ[D.host.F] (o * m) := by
  have e : toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m =
      toCompl h (b ⊗ₜ[D.host.F] (o * m)) := by
    rw [toCompl_tmul, toCompl_tmul, map_mul, mul_assoc]
  have e2 : toCompl h (b ⊗ₜ[D.host.F] (o * m)) = GlobalTheory.LFun.InertChart.complEquiv hw h (b ⊗ₜ[D.host.F] (o * m)) := rfl
  rw [e, e2]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) = _
  rw [RingEquiv.symm_apply_apply, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]

theorem secW_rank_one_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ frameLat S)
    {t : Fin T.rank → D.host.E} (ht : t ∈ frameLat T) {z : w.adicCompletion D.host.E} (hz : z ∈ Ov D.host.E w) :
    (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E)
      (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  obtain ⟨y, rfl⟩ := GlobalTheory.LFun.InertChart.toCompl_surjective h z
  have hy := (GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h y).2 hz
  refine intLoc_induction (p := fun y => (Matrix.of fun i j => secW hw h (toCompl h y *
      algebraMap D.host.E (w.adicCompletion D.host.E) (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v)) (fun b hb o => ?_) ?_ (fun y y' h1 h2 => ?_)
      (fun y h1 => ?_) hy
  · refine AddSubgroup.subset_closure ⟨singleFin v b, fun u => ?_, fun u hu => evalV_singleFin_ne hu _, a, ha, s, hs,
      o • t, Submodule.smul_mem _ o ht, ?_⟩
    · by_cases e : u = v
      · subst e; rw [evalV_singleFin_self]; exact hb
      · rw [evalV_singleFin_ne e]; exact zero_mem _
    · ext i j
      rw [Matrix.of_apply, Matrix.of_apply, secW_toCompl_tmul_mul]
      congr 1
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
  · convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  · convert add_mem h1 h2 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, map_add (f := _), add_mul]
  · convert neg_mem h1 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, map_neg, neg_mul]

theorem secW_span_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : IsConjAt D.sp.cm.sig h c) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {p : Fin T.rank → w.adicCompletion D.host.E} (hp : p ∈ latAt w (frameLat T))
    {y : Fin S.rank → w.adicCompletion D.host.E} (hy : y ∈ latAt w (frameLat S)) :
    ∀ z ∈ Ov D.host.E w, (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E) a * p i *
      ∑ k, c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  have hst : ∀ x : D.host.E, star x = D.sp.cm.sig x := fun _ => rfl
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t, ht, rfl⟩ := hp
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      intro z hz
      convert secW_rank_one_mem hw h ha hs ht hz using 1
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.of_apply, GlobalTheory.LFun.InertChart.conj_algebraMap hc, map_mul, map_sum, hst]
      ring_nf
    | zero =>
      intro z hz
      convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
      ext i j
      simp
    | add y y' _ _ h1 h2 =>
      intro z hz
      convert add_mem (h1 z hz) (h2 z hz) using 1
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add]
    | smul o y _ h1 =>
      intro z hz
      convert h1 (z * c o) (mul_mem hz (GlobalTheory.LFun.InertChart.conj_mem hw hc o.2)) using 1
      ext i j
      have e : ∀ k, c ((o • y) k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j) =
          c o * (c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) := fun k => by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, mul_assoc]
      simp only [Matrix.of_apply, e, ← Finset.mul_sum]
      congr 1
      ring
  | zero =>
    intro z hz
    convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  | add p p' _ _ h1 h2 =>
    intro z hz
    convert add_mem (h1 z hz) (h2 z hz) using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul, mul_add]
  | smul o p _ h1 =>
    intro z hz
    convert h1 (z * o) (mul_mem hz o.2) using 1
    ext i j
    simp only [Matrix.of_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    congr 1
    ring

theorem uPt_mem_latO : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → uPt hw h k aS aT x ∈ latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  intro D v w hw h S T k aS aT hk haS haT x hx
  obtain ⟨-, ⟨a₀, ha₀, rfl⟩, -⟩ := hk
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt D.sp.cm.sig hw h
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (isCMExt_host D) hw hc
  have hcc : ∀ z, c (c z) = z := hU.1
  set ι := algebraMap D.host.E (w.adicCompletion D.host.E) with hι
  set Gw := S.gram.map ι with hGw
  set Gi := (S.gram⁻¹).map ι with hGi
  have hGG : Gi * Gw = 1 := by
    rw [hGi, hGw, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  set N := (aS⁻¹).1 * Gi with hN
  have hG : ∀ l i, c (ι (S.gram l i)) = ι (S.gram i l) := fun l i => by
    rw [GlobalTheory.LFun.InertChart.conj_algebraMap hc, (GlobalTheory.Doubling.isHermND_gram S).1 i l]
  have hY : ∀ j, (fun l => c (N j l)) ∈ latAt w (frameLat S) := by
    intro j
    rw [GlobalTheory.LFun.InertChart.mem_latAt_iff hw hc (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D S v)]
    intro y hy
    have hu := (haS ((aS⁻¹).1 *ᵥ y)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) j
    have e : Formalism.UG.hform c (S.gram.map ι) y (fun l => c (N j l)) = c ((N *ᵥ (Gw *ᵥ y)) j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hG, hGw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, Matrix.mulVec_mulVec, hN, Matrix.mul_assoc, hGG, Matrix.mul_one]
    exact GlobalTheory.LFun.InertChart.conj_mem hw hc hu
  have hcol : ∀ j l, ∑ m, c (c (N j m)) * ι (S.gram m l) = (aS⁻¹).1 j l := fun j l => by
    simp only [hcc]
    have := congrFun (congrFun (show N * Gw = (aS⁻¹).1 by rw [hN, Matrix.mul_assoc, hGG, Matrix.mul_one]) j) l
    rw [← this, Matrix.mul_apply]
    rfl
  have hT : ∀ i, (fun r => aT.1 r i) ∈ latAt w (frameLat T) := fun i => by
    have := (haT (Pi.single i 1)).1 fun m => by
      by_cases e : m = i
      · subst e; simp
      · simp [e]
    convert this using 1
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdec : uPt hw h (ι a₀) aS aT x = ∑ i, ∑ j, (Matrix.of fun r l => secW hw h (x i j * ι a₀ * aT.1 r i *
      ∑ m, c (c (N j m)) * ι (S.gram m l)) : WO S T) := by
    ext r l
    simp only [uPt, Matrix.map_apply, Matrix.sum_apply, Matrix.of_apply, hcol]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ∀ f : Fin T.rank → Fin S.rank → w.adicCompletion D.host.E, ∑ i, ∑ j, secW hw h (f i j) =
        secW hw h (∑ i, ∑ j, f i j) from fun f => by simp only [map_sum]]
    congr 1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdec]
  exact sum_mem fun i _ => sum_mem fun j _ => secW_span_mem hw h hc ha₀ (hT i) (hY j) (x i j) (hx i j)

end GlobalTheory.InertFrameLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertSupportedPointIntegralFramesMemLatticeStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_supported_point_integral_frames_mem_lattice : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → uPt hw h k aS aT x ∈ latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  first | exact @GlobalTheory.InertFrameLoc.uPt_mem_latO | exact GlobalTheory.InertFrameLoc.uPt_mem_latO | (intros; apply GlobalTheory.InertFrameLoc.uPt_mem_latO <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupActionInertSupportedPointsFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupActionInertSupportedPointsFrames
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameAct

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem compW_eq_toCompl (h : w.under (𝓞 D.host.F) = v) (a : AE D) :
    GlobalTheory.InertHomIdx.compW D w a = toCompl h (GlobalTheory.AdelicU.compFin D.host.F D.host.E v a) := by
  show finAdEquiv D.host.F D.host.E (finPart D a) w = _
  rw [finAdEquiv_apply h, ← GlobalTheory.EmbChart.map_evalV_map_sndA]
  rfl

theorem secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z : w.adicCompletion D.host.E) (a : AE D) :
    secW hw h z * a = secW hw h (z * GlobalTheory.InertHomIdx.compW D w a) := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((InertChart.complEquiv hw h).symm z) * a =
    GlobalTheory.EmbChart.tensAt D.host.E v ((InertChart.complEquiv hw h).symm (z * GlobalTheory.InertHomIdx.compW D w a))
  rw [GlobalTheory.EmbChart.tensAt_mul_right]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, compW_eq_toCompl h]
  rfl

theorem mul_secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z : w.adicCompletion D.host.E) (a : AE D) :
    a * secW hw h z = secW hw h (GlobalTheory.InertHomIdx.compW D w a * z) := by
  rw [mul_comm, secW_mul, mul_comm]

theorem mul_map_secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) (AE D)) (M : Matrix (Fin n) (Fin p) (w.adicCompletion D.host.E)) :
    A * M.map (secW hw h) = (A.map (GlobalTheory.InertHomIdx.compW D w) * M).map (secW hw h) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, mul_secW]

theorem map_secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {m n p : ℕ}
    (M : Matrix (Fin m) (Fin n) (w.adicCompletion D.host.E)) (B : Matrix (Fin n) (Fin p) (AE D)) :
    M.map (secW hw h) * B = (M * B.map (GlobalTheory.InertHomIdx.compW D w)).map (secW hw h) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, secW_mul]

end GlobalTheory.InertFrameAct


open GlobalTheory.InertFrameAct in
theorem GlobalTheory.InertFrameAct.actO_uPt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) (gS : Gv S v) (gT : Gv T v) (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)), actO S T (embV S v gS) (embV T v gT) (uPt hw h k aS aT x) = uPt hw h k aS aT ((aT⁻¹ * locMat D.sp.cm.sig T.gram h gT * aT).1 * x * (aS⁻¹ * locMat D.sp.cm.sig S.gram h gS⁻¹ * aS).1) := by
  intro D v w hw h S T k aS aT gS gT x
  have hT : (mt T (embV T v gT)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h gT).1 := by
    have e := finMat_map_compAt D.sp.cm.sig T.gram h (embV T v gT)
    rw [proj_emb_self] at e
    exact e
  have hS : (mt S (embV S v gS⁻¹)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig S.gram h gS⁻¹).1 := by
    have e := finMat_map_compAt D.sp.cm.sig S.gram h (embV S v gS⁻¹)
    rw [proj_emb_self] at e
    exact e
  have hinv : (embV S v gS)⁻¹ = embV S v gS⁻¹ := (map_inv _ _).symm
  rw [actO, uPt, uPt, hinv, mul_map_secW, map_secW_mul, hT, hS]
  congr 1
  have h1 : aT.1 * (aT⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : aS.1 * (aS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [h2, Matrix.mul_one]
  rw [← Matrix.mul_assoc aT.1 (aT⁻¹).1, h1, Matrix.one_mul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupActionInertSupportedPointsFramesStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_group_action_inert_supported_points_frames : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) (gS : Gv S v) (gT : Gv T v) (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)), actO S T (embV S v gS) (embV T v gT) (uPt hw h k aS aT x) = uPt hw h k aS aT ((aT⁻¹ * locMat D.sp.cm.sig T.gram h gT * aT).1 * x * (aS⁻¹ * locMat D.sp.cm.sig S.gram h gS⁻¹ * aS).1) := by
  first | exact @GlobalTheory.InertFrameAct.actO_uPt | exact GlobalTheory.InertFrameAct.actO_uPt | (intros; apply GlobalTheory.InertFrameAct.actO_uPt <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticFormInertSupportedPointsAntidiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticFormInertSupportedPointsAntidiagonal
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameSympl

open Formalism.UG (cT cT_mul cT_one antiJ)
open GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v}

def evW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_apply (z : w.adicCompletion D.host.E) :
    secW hw h z = GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) := rfl

theorem secW_mul_right (z : w.adicCompletion D.host.E) (A : AE D) :
    secW hw h z * A = secW hw h (z * evW hw h A) := by
  rw [secW_apply, secW_apply, GlobalTheory.EmbChart.tensAt_mul_right]
  congr 1
  rw [map_mul (GlobalTheory.LFun.InertChart.complEquiv hw h).symm]
  show _ = _ * (GlobalTheory.LFun.InertChart.complEquiv hw h).symm ((GlobalTheory.LFun.InertChart.complEquiv hw h) _)
  rw [RingEquiv.symm_apply_apply]

theorem evW_secW (z : w.adicCompletion D.host.E) : evW hw h (secW hw h z) = z := by
  show GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v (GlobalTheory.EmbChart.tensAt D.host.E v
    ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z))) = z
  rw [GlobalTheory.EmbChart.compFin_tensAt, RingEquiv.apply_symm_apply]

theorem evW_incA (a : D.host.E) : evW hw h (incA D a) = algebraMap D.host.E _ a := by
  show GlobalTheory.LFun.toCompl h (compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] a)) = _
  show GlobalTheory.LFun.toCompl h ((evFin D.host.F v 1) ⊗ₜ[D.host.F] a) = _
  rw [map_one, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

theorem incA_mul_secW (a : D.host.E) (z : w.adicCompletion D.host.E) :
    incA D a * secW hw h z = secW hw h (algebraMap D.host.E _ a * z) := by
  rw [mul_comm, secW_mul_right, evW_incA, mul_comm]

theorem cA_secW {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : cA D (secW hw h z) = secW hw h (c z) := by
  rw [secW_apply, secW_apply]
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (GlobalTheory.EmbChart.tensAt D.host.E v _) = GlobalTheory.EmbChart.tensAt D.host.E v _
  rw [GlobalTheory.EmbChart.sigR_tensAt]
  congr 1
  apply (GlobalTheory.LFun.InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply]
  have := hc ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)
  exact this.symm.trans (congrArg c ((GlobalTheory.LFun.InertChart.complEquiv hw h).apply_symm_apply z))

theorem hO_map_secW {S T : HSp D} {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c) (M N : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (M.map (secW hw h)) (N.map (secW hw h)) = secW hw h (Matrix.trace
      ((S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      cT c N * (T.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin T.rank) (Fin T.rank) _) * M)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hO, Matrix.map_apply, cA_secW hc, incA_mul_secW, secW_mul_right, evW_incA, evW_secW, ← map_sum]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Matrix.map_apply, cT, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]

variable {L : Type} [Field L]

theorem cT_smul' (c : L →+* L) {m n : ℕ} (k : L) (A : Matrix (Fin m) (Fin n) L) : cT c (k • A) = c k • cT c A := by
  ext i j
  simp [cT, Matrix.smul_apply]

theorem inv_eq_of_frame (c : L →+* L) {n : ℕ} {G G' : Matrix (Fin n) (Fin n) L} (hG : G' * G = 1) (a : GL (Fin n) L)
    (ha : cT c a.1 * G * a.1 = antiJ L n) : G' = a.1 * antiJ L n * cT c a.1 := by
  have h1 : G * a.1 = cT c (a⁻¹).1 * antiJ L n := by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul]
  have h2 : G * (a.1 * antiJ L n * cT c a.1) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (cT c (a⁻¹).1),
      Formalism.UG.P.fIwasawa_antiJ_mul_antiJ, Matrix.mul_one, ← cT_mul, Units.mul_inv, cT_one]
  rw [← Matrix.mul_one G', ← h2, ← Matrix.mul_assoc, hG, Matrix.one_mul]

theorem trace_frame (c : L →+* L) {n n' : ℕ} (k : L) (aS : GL (Fin n) L) (aT : GL (Fin n') L)
    (GT J' : Matrix (Fin n') (Fin n') L) (J : Matrix (Fin n) (Fin n) L) (hT : cT c aT.1 * GT * aT.1 = J')
    (x y : Matrix (Fin n') (Fin n) L) :
    Matrix.trace (aS.1 * J * cT c aS.1 * cT c (k • (aT.1 * y * (aS⁻¹).1)) * GT * (k • (aT.1 * x * (aS⁻¹).1))) =
      k * c k * Matrix.trace (J * cT c y * J' * x) := by
  rw [cT_smul', cT_mul, cT_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT c aS.1) (cT c (aS⁻¹).1), ← cT_mul, Units.inv_mul, cT_one, Matrix.one_mul,
    ← Matrix.mul_assoc GT aT.1, ← Matrix.mul_assoc (cT c aT.1) (GT * aT.1), ← Matrix.mul_assoc (cT c aT.1) GT, hT, Matrix.trace_mul_comm aS.1]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  ring

theorem hO_uPt {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v} {S T : HSp D}
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (k : w.adicCompletion D.host.E)
    {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)} {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (hS : cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = antiJ _ S.rank)
    (hT : cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = antiJ _ T.rank)
    (x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (uPt hw h k aS aT x) (uPt hw h k aS aT y) =
      secW hw h (k * c k * Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x)) := by
  have hG : (S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      S.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [uPt, uPt, hO_map_secW hc, inv_eq_of_frame c hG aS hS, trace_frame c k aS aT _ _ _ hT]

theorem symplOH_uPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsConjAt D.sp.cm.sig h c → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), ψ (symplOH S T (uPt hw h k aS aT x) (uPt hw h k aS aT y)) = thW ψ hw h (k * c k) (2⁻¹ * GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y) := by
  intro D ψ v w hw h S T c k aS aT hc hS hT x y
  have h2 : (2 : w.adicCompletion D.host.E) ≠ 0 := by
    have : CharZero (w.adicCompletion D.host.E) := algebraRat.charZero _
    exact two_ne_zero
  have hx : (2⁻¹ : w.adicCompletion D.host.E) • x + (2⁻¹ : w.adicCompletion D.host.E) • x = x := by
    rw [← add_smul, ← two_mul, mul_inv_cancel₀ h2, one_smul]
  have hl : GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y =
      Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x) := by
    rw [GlobalTheory.Hk3.locH, one_mul]
    rfl
  conv_lhs => rw [← hx, uPt_add, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self]
  rw [thW_apply, symplO, hO_uPt k hc hS hT, hl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]

end GlobalTheory.InertFrameSympl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticFormInertSupportedPointsAntidiagonalStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_inert_supported_points_antidiagonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsConjAt D.sp.cm.sig h c → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), ψ (symplOH S T (uPt hw h k aS aT x) (uPt hw h k aS aT y)) = thW ψ hw h (k * c k) (2⁻¹ * GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y) := by
  first | exact @GlobalTheory.InertFrameSympl.symplOH_uPt | exact GlobalTheory.InertFrameSympl.symplOH_uPt | (intros; apply GlobalTheory.InertFrameSympl.symplOH_uPt <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalCharacterConjugationInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalCharacterConjugationInverse
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem secW_cA (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (hc : IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : secW hw h (c z) = cA D (secW hw h z) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.LFun.InertChart.complEquiv hw h).surjective z
  have e1 : c (GlobalTheory.LFun.InertChart.complEquiv hw h y) =
      GlobalTheory.LFun.InertChart.complEquiv hw h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig y) := hc y
  rw [e1]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) =
    cA D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _))
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  exact (GlobalTheory.EmbChart.sigR_tensAt v _ y).symm

theorem thW_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsConjAt D.sp.cm.sig h c → (∀ z, c (c z) = z) → ∀ z, thW ψ hw h (k * c k) (c z) * thW ψ hw h (k * c k) z = 1 := by
  intro D ψ v w hw h c k hc hcc z
  have h1 : secW hw h (k * c k * c z) = cA D (secW hw h (k * c k * z)) := by
    rw [← secW_cA D hw h c hc]
    congr 1
    rw [map_mul c, map_mul c, hcc, mul_comm k (c k)]
  rw [thW_apply, thW_apply, h1, ← GlobalTheory.DualPairCheck.trace_cA (_ * cA D _), RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, neg_mul, LinearMap.map_neg,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.InertFrameLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalCharacterConjugationInverseStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_local_character_conjugation_inverse : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsConjAt D.sp.cm.sig h c → (∀ z, c (c z) = z) → ∀ z, thW ψ hw h (k * c k) (c z) * thW ψ hw h (k * c k) z = 1 := by
  first | exact @GlobalTheory.InertFrameLoc.thW_conj | exact GlobalTheory.InertFrameLoc.thW_conj | (intros; apply GlobalTheory.InertFrameLoc.thW_conj <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardLocalisationWeilDatumInertPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertFrameLoc


set_option maxHeartbeats 800000 in
theorem exists_isStd_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ (∀ m : M, IsThetaFunO ψ S T m) ∧ ∀ x, ∃ u : WO S T, ∀ m : M, ((ρ x m : M) : WO S T → ℂ) = heisO ψ S T u m := by
  intro D ψ S T χS χT om hW v w h hw uS uT c ϖ eS eT hU hcS hcT f hf hf0
  obtain ⟨hconj, ⟨aS, haS, gS, eSa⟩, kSc⟩ := hcS
  obtain ⟨-, ⟨aT, haT, gT, eTa⟩, kTc⟩ := hcT
  obtain ⟨k, hk⟩ := GlobalTheory.InertLoc.exists_isGen D w
  have h2 := GlobalTheory.T.valued_two_eq_one_inertPlace_cmField D v w hw
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := GlobalTheory.InertLoc.exists_delta_psi hU h2 (thW ψ hw h (k * c k))
    (GlobalTheory.T.inert_place_local_character_conjugation_inverse D ψ v w hw h c k hconj hU.1) (GlobalTheory.T.inertPlace_localTraceCharacter_conductor_integers D ψ v w hw h c ϖ k hW.std hconj hU hk)
  have hadd : ∀ x y, uPt hw h k aS aT (x + y) = uPt hw h k aS aT x + uPt hw h k aS aT y := uPt_add
  have hMθ : spanT ψ (uPt hw h k aS aT) f ≤ GlobalTheory.FinWeilO.thetaSub ψ S T := Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    exact GlobalTheory.FinTranslate.isTheta_heisO_fin hW.std.1 (map_infPart_uPt (hw := hw) (h := h) (k := k) (aS := aS) (aT := aT) x) hf.1)
  let π : GU c S.rank × GU c T.rank →* Module.End ℂ (WO S T → ℂ) :=
    om.comp (((embV S v).comp eS.symm.toMonoidHom).prodMap ((embV T v).comp eT.symm.toMonoidHom))
  have hπ : ∀ p m, π p m = om (embV S v (eS.symm p.1), embV T v (eT.symm p.2)) m := fun _ _ => rfl
  have hstab : ∀ p, ∀ m ∈ spanT ψ (uPt hw h k aS aT) f, π p m ∈ spanT ψ (uPt hw h k aS aT) f := fun p m hm =>
    mem_spanT_of (fun y => by
      rw [hπ, hW.om_heis _ _ _ _ hf.1, GlobalTheory.T.local_group_action_inert_supported_points_frames]
      exact heis_mem_spanT hadd _
        (GlobalTheory.T.weilRep_latticeVacuum_mem_span_inertTranslates D ψ S T χS χT om hW v w hw h uS uT c ϖ k aS aT hU hconj hk haS haT gS gT f hf _ _)) hm
  have hint2 : (2⁻¹ : w.adicCompletion D.host.E) ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := (GlobalTheory.SphTheta.half h2).2
  have hvac : ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E),
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → heisO ψ S T (uPt hw h k aS aT x) f = f := fun x hx => by
    have h1 := hf.2.1 _ (GlobalTheory.T.inert_supported_point_integral_frames_mem_lattice D v w hw h S T k aS aT hk haS haT ((2⁻¹ : w.adicCompletion D.host.E) • x)
      fun i j => mul_mem hint2 (hx i j))
    rwa [two_nsmul, ← uPt_add, GlobalTheory.InertLoc.half_add_half] at h1
  have hfM : f ∈ spanT ψ (uPt hw h k aS aT) f := self_mem_spanT uPt_zero
  have dict := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have unr : ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → GlobalTheory.Hk3.UnrPl w χ := fun χ hχ =>
    dict.2.1 χ fun w' hw' => by rw [(GlobalTheory.LFun.InertChart.under_eq_iff hw w').1 hw']; exact hχ
  have hfix := GlobalTheory.ConjVacFix.vacFix_of_unrPl ψ S T χS χT om w hW (unr χS uS) (unr χT uT)
  refine ⟨δ, ψ', spanT ψ (uPt hw h k aS aT) f, rhoT ψ (uPt hw h k aS aT) f hadd, omT ψ (uPt hw h k aS aT) f π hstab,
    ⟨f, hfM⟩, ⟨⟨hU, GlobalTheory.InertLoc.odd_of_v_two hU h2, antiG_mem _, antiG_mem _, antiJ_herm c _, antiJ_herm c _, hδ, p1, p2,
      ?_, fun x y => ?_, ?_, fun g g' x => ?_, fun g g' hg hg' s hs => ?_⟩,
      fun e => hf0 (congrArg Subtype.val e), fun x hx => Subtype.ext (hvac x hx), span_rhoT_eq_top hadd hfM⟩,
    rfl, fun _ _ _ => rfl, fun m => hMθ m.2, fun x => ⟨uPt hw h k aS aT x, fun _ => rfl⟩⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [coe_rhoT, uPt_zero, GlobalTheory.SplitScalar.heisO_zero]
    rfl
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [Module.End.mul_apply, coe_rhoT, coe_rhoT, GlobalTheory.SplitScalar.heisO_heisO, LinearMap.smul_apply, Submodule.coe_smul,
      coe_rhoT, ← uPt_add, GlobalTheory.T.symplectic_form_inert_supported_points_antidiagonal D ψ v w hw h S T c k aS aT hconj gS gT, ← p3]
    simp only [GlobalTheory.Hk3.locH, one_mul]
  · refine eq_top_iff.2 ((span_rhoT_eq_top hadd hfM).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨x, rfl⟩
    exact ⟨x, ⟨f, hfM⟩, fun y hy => Subtype.ext (hvac y hy), rfl⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    have hinv : (eS.symm g)⁻¹ = eS.symm g⁻¹ := (map_inv eS.symm g).symm
    show π (g, g') (heisO ψ S T (uPt hw h k aS aT x) m) = heisO ψ S T (uPt hw h k aS aT _) (π (g, g') m)
    rw [hπ, hπ, hW.om_heis _ _ _ _ (hMθ m.2), GlobalTheory.T.local_group_action_inert_supported_points_frames]
    refine congrArg (fun z => heisO ψ S T (uPt hw h k aS aT z) (om (embV S v (eS.symm g), embV T v (eT.symm g')) m)) ?_
    rw [← eTa, hinv, ← eSa]
    erw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  · refine Subtype.ext (hfix _ ⟨hMθ s.2, fun e e' he uu huu hh => ?_⟩ _
      ((dict.2.2.1 S _).2 ⟨eS.symm g, (kSc _).2 ((eS.apply_symm_apply g).symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg), rfl⟩) _
      ((dict.2.2.1 T _).2 ⟨eT.symm g', (kTc _).2 ((eT.apply_symm_apply g').symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg'), rfl⟩))
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.exists_integralFramePoint_of_inertHalf_latticePoint D v w hw h S T k aS aT hk haS haT e e' he uu huu hh
    exact congrArg Subtype.val (hs x hx)

end GlobalTheory.InertFrameLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardLocalisationWeilDatumInertPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardLocalisation_weilDatum_inertPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ (∀ m : M, IsThetaFunO ψ S T m) ∧ ∀ x, ∃ u : WO S T, ∀ m : M, ((ρ x m : M) : WO S T → ℂ) = heisO ψ S T u m := by
  first | exact @GlobalTheory.InertFrameLoc.exists_isStd_inert | exact GlobalTheory.InertFrameLoc.exists_isStd_inert | (intros; apply GlobalTheory.InertFrameLoc.exists_isStd_inert <;> assumption)
end
