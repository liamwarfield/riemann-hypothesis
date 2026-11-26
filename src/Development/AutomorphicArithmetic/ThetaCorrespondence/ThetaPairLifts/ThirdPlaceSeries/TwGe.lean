module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtremalVectorsSplitPartStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatIoAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGenCx
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGenCx
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwCx
open GlobalTheory.ExportSeries Formalism.IndefR.Datum GlobalTheory.BigOn.Exp.TupLe GlobalTheory.BigOn.Exp.SerBase
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem cx_at_alt (s1 : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition) (s2 : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition) (s3 : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition) (s6 : TwQ) (hr : p.PointConditions') (hm : More p)
    (hw : D.plEq w ∈ p.R.twPl)
    (hok : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) {ν : ℂ} (hfit : Fit p w j hρ ν)
    (hLS : ∀ h, ∀ P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h,
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hLI : LatIo p w j)
    (c1 : ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w))
    (c2 : p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi)
    (e : FractionRing (ex.nch.Oe w) →+* ℂ)
    (h2 : ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a)
    (z : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w))
    (hz : z ∈ twSet hρ (rdAt p w j hρ ν) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)) :
    ∃ (n : ℕ) (h : Fin n → GA D (Vc D j)) (w' : Fin n → ((R2 p).cV j).W) (a : Fin n → ex.nch.Oe w) (κ : ℂ) (N : ℕ),
    IsUnit ((N : ℕ) : ex.nch.Oe w) ∧ (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) ∧
    (∀ k, h k ∈ GfC (Vc D j) ∧ InCoefLat (R2 p) j (h k) (w' k)) ∧
    ∀ y : Fin n → Fin ((R2 p).nW j) → D.what₂.LL,
      (∀ k, ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ, adForm (R2 p) j (y k) (fun τ => v τ) =
        levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
          ((R2 p).vP j ((R2 p).mu (D.plEq w))) (h k) (w' k) v)) →
      rdK (rdAt p w j hρ ν) hρ (ex.nch.k' w) z = κ • ∑ k, (e (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)) (a k)) * ν⁻¹) •
        adForm (R2 p) j (y k) (p.v₀ j (sg0 D p.P.A3.A)) := by
  obtain ⟨hadapt, hν, -, hlev⟩ := hfit
  have hpin := hadapt.1
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hB0 : BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) :=
    { baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin (ex.nch.twI w) j (ex.nch.sd w) with }
  obtain ⟨p1, p2, p3⟩ := s1 _ _ _ _ _ _ _ _ _ _ p j hr hm w hw hok ρ hρ hpin c1 c2
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good _ _ _ ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  have hB := hρ.base (ex.nch.twI w) j (ex.nch.sd w)
  obtain ⟨z0, cz, hz0, hcz, hfl⟩ := s2 _ _ _ _ _ _ _ _ _ _ p j hr hm _ _ ((R2 p).mu (D.plEq w)) hB hB0 ht hadm c2 p3
  have hzf : z0 ∈ GfC (Vc D j) := GlobalTheory.TwTraceCx.mem_GfC_of_suppAt p1 hz0
  have hω : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).IsWeil
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi
      ((R2 p).ωP j ((R2 p).mu (D.plEq w))) := by
    have e0 : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).mu *
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi =
        (R2 p).toLevCh.mu ((R2 p).mu (D.plEq w)) ((j : ℕ) + 1) := by
      rw [Base.mu, hB0.mu0, mul_assoc, ← c2]
      rfl
    rw [Base.IsWeil, e0, hB0.ψ, hB0.eta]
    exact hC.thP.ωP j _
  have hN : IsUnit ((GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w)) : ℕ) : ex.nch.Oe w) := by
    have hcop : Nat.Coprime (D.ntw.l (ex.nch.twI w)) (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
      have := GlobalTheory.NormUnit.coprime_absNorm _ (D.ntw.lPrime _).out P (p2 P hP)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    simpa using (GlobalTheory.NormUnit.isUnit_natCast_of_coprime (D.ntw.O_l _) hcop).map (algebraMap _ (ex.nch.Oe w))
  obtain ⟨ν0, c, hs, n, hn, hνc⟩ := hν
  rw [p.phsOne j, map_one, one_mul] at hνc
  have c0 : c ≠ 0 := fun h => ν0 (by rw [h, zero_pow hn] at hνc; exact pow_eq_zero_iff hn |>.1 hνc)
  obtain ⟨u, hu, hio⟩ := hLI ρ hρ hpin c c0 hs
  obtain ⟨s, h, P, hd, hQ, hsupp, hgen⟩ := hz
  have hq1 := ht.split
  have hq2 : ∀ P' ∈ (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q,
      ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal :=
    fun P' hP' => s6 D _ _ _ _ hok P' (mem_half.1 hP').1
  have hP1 := lat_translate_of_prime hρ _ j _ hq1 hq2 hsupp hd.mem
  have hP2 := lat_translate_of_prime hρ _ j _ p1 p2 (GlobalTheory.DownLift.SplitCoef.suppAt_inv_of hz0) hP1
  have hh2 : h * hQ * z0⁻¹ ∈ GfC (Vc D j) :=
    mul_mem (mul_mem hd.fin (GlobalTheory.TwTraceCx.mem_GfC_of_suppAt hq1 hsupp)) (inv_mem hzf)
  obtain ⟨n', f, g, hsum⟩ := Submodule.mem_span_set'.1 (hLS _ P hP2)
  choose y hy hyio using fun k => hio _ hh2 (g k).1 (g k).2
  choose o ho using fun k => RingHom.mem_range.1 (f k).2
  obtain ⟨uu, huu⟩ := hval (detRoot (Vc D j) (h * hQ))
  have hcu : UnitOff (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) (cz * (c⁻¹ * ν)) :=
    unitOff_mul hcz (unitOff_root hn (by rw [mul_pow, inv_pow, hνc, inv_mul_cancel₀ (pow_ne_zero _ c0)]))
  obtain ⟨-, m, hm1, -⟩ := hcu
  refine ⟨n', fun _ => h * hQ * z0⁻¹, y,
    fun k => algebraMap _ (ex.nch.Oe w) ((uu : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) * algebraMap _ _ (o k)),
    cz * (c⁻¹ * ν), _, hN, ⟨m, hm1⟩, fun k => ⟨hh2, hy k⟩, ?_⟩
  intro yy hyy
  have eA : ∀ k, adForm (R2 p) j (yy k) (p.v₀ j (sg0 D p.P.A3.A)) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
      (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu (D.plEq w))) ((R2 p).vP j ((R2 p).mu (D.plEq w)))
        (h * hQ * z0⁻¹) (y k) u) := fun k =>
    (congrArg (adForm (R2 p) j (yy k)) (funext hu)).symm.trans (hyy k u)
  have eE : ∀ k, e (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)) (algebraMap _ (ex.nch.Oe w)
      ((uu : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) * algebraMap _ _ (o k)))) =
      ((detChar (Vc D j) (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w)
        (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (h * hQ) : Circle) : ℂ) * (f k : ℂ) := fun k => by
    rw [h2, map_mul, hρ.ek_e, ho k, ← huu]
    rfl
  have eS : ∀ k, series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
      ((princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecFlat
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)))
      (h * hQ) (g k : PolF D (Wc D j).rank (Vc D j).rank) = (c⁻¹ * cz) •
      singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu (D.plEq w))) ((R2 p).vP j ((R2 p).mu (D.plEq w)))
        (h * hQ * z0⁻¹) (y k) u := fun k => by
    have e1 : (g k : PolF D (Wc D j).rank (Vc D j).rank) = c⁻¹ • (R2 p).ioP j (PiTensorProduct.tprod ℂ u) (y k) := by
      rw [hyio k, smul_smul, inv_mul_cancel₀ c0, one_smul]
    rw [e1, map_smul, hB0.series_eq_ser, hfl]
    funext g'
    have e3 := GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class _ _ _ _ _ _ (R2 p) _ hC j ((R2 p).mu (D.plEq w)) z0⁻¹ cz (inv_mem hzf) u (h * hQ) (y k) g'
    simp only [Pi.smul_apply, smul_eq_mul] at e3 ⊢
    rw [e3]
    simp only [GlobalTheory.ConjTwist.ser, singleSeries]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hgen, GlobalTheory.TwTraceCx.gen_eq_smul hB ht hadm (hρ.weil_base _ _ _) hω,
    ← s3 _ _ _ _ _ _ _ _ _ _ p j hr hm ρ hρ hpin hlev _ _ _ _ ht hadm hω, ← hsum, map_sum, map_sum]
  simp only [Subring.smul_def, map_smul, eS, eA, eE, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  field_simp
end Point
theorem twGen_cx_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ z ∈ twSet hρ (rdAt p w j hρ ν) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w) (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w),
  ∃ (n : ℕ) (h : Fin n → GA (Fm.D x i) (Vc (Fm.D x i) j)) (w' : Fin n → ((R2 p).cV j).W) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (κ : ℂ) (N : ℕ),
    IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) ∧ (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) ∧
    (∀ k, h k ∈ GfC (Vc (Fm.D x i) j) ∧ InCoefLat (R2 p) j (h k) (w' k)) ∧
    ∀ y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL,
      (∀ k, ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j (y k) (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) (h k) (w' k) v)) →
      rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun _ _ _ _ hAdm hChr =>
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hAdm (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hChr (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and _root_.GlobalTheory.T.latSmallGen' _root_.GlobalTheory.T.latIoAt'))) fun Fm x hx i p hr hm w hw j ⟨a1, a2, a4, a5⟩ ρ hρ ν _ hfit _ e _ h2 z hz =>
    let ⟨c1, c2⟩ := a2 ρ hρ hfit.1
    _root_.GlobalTheory.BigOn.Exp.TwCx.cx_at_alt _root_.GlobalTheory.T.seesaw_places_statement _root_.GlobalTheory.T.tuple_flat_estimate _root_.GlobalTheory.T.tupLe_traceSt twQ hr hm hw a1.1 hρ hfit (a4 ρ hρ hfit.1.1) a5 c1 c2 e h2 z hz
end GlobalTheory.BigOn.Exp.TwCx
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGenCxStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_embedding_compatibility_rows_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ z ∈ twSet hρ (rdAt p w j hρ ν) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w) (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w),
  ∃ (n : ℕ) (h : Fin n → GA (Fm.D x i) (Vc (Fm.D x i) j)) (w' : Fin n → ((R2 p).cV j).W) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (κ : ℂ) (N : ℕ),
    IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) ∧ (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) ∧
    (∀ k, h k ∈ GfC (Vc (Fm.D x i) j) ∧ InCoefLat (R2 p) j (h k) (w' k)) ∧
    ∀ y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL,
      (∀ k, ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j (y k) (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) (h k) (w' k) v)) →
      rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TwCx.twGen_cx_alt | exact _root_.GlobalTheory.BigOn.Exp.TwCx.twGen_cx_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TwCx.twGen_cx_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelTracedSeriesRational
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipal
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipal
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TieLift
theorem lift_principal_alt : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
    ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hr hm w hw j g0 =>
    GlobalTheory.GalLift.Transl.lifts (R2 p) j (_root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1).1.lev g0
end GlobalTheory.TieLift
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipalStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLevelLift_at_twisted_points : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
  ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' := by
  first | exact @_root_.GlobalTheory.TieLift.lift_principal_alt | exact _root_.GlobalTheory.TieLift.lift_principal_alt | (intros; apply _root_.GlobalTheory.TieLift.lift_principal_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiVal
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiVal
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.LevVal
theorem chi_val_alt : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ k, ∃ a : (Fm.D x i).what₂.LL,
  (Fm.D x i).what₂.embLL a = (((GlobalTheory.TraceIncl.envV (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w))).χ k : ℂˣ) : ℂ) :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun _ _ _ _ p hr hm _ _ j k =>
    envV_chi_mem (R2 p) (F2 p) (_root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1).1 j _ k
end GlobalTheory.BigOn.LevVal
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiValStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_character_rational_values' : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ k, ∃ a : (Fm.D x i).what₂.LL,
  (Fm.D x i).what₂.embLL a = (((GlobalTheory.TraceIncl.envV (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w))).χ k : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.BigOn.LevVal.chi_val_alt | exact _root_.GlobalTheory.BigOn.LevVal.chi_val_alt | (intros; apply _root_.GlobalTheory.BigOn.LevVal.chi_val_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelTracedSeriesRational
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.Exp
theorem adForm_eq_levelTrace_singleSeries' : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ h ∈ GfC (Vc (Fm.D x i) j), ∀ w' : ((R2 p).cV j).W, InCoefLat (R2 p) j h w' →
  ∃ y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)), ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j y (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) h w' v) := by
  intro _ _ _ _
  have hR := _root_.GlobalTheory.T.rational_estimate_statement'
  have hC := _root_.GlobalTheory.T.twisted_character_rational_values'
  have hN := _root_.GlobalTheory.T.exists_isLevelLift_at_twisted_points
  unfold _root_.GlobalTheory.BigOn.RationalityStatement' _root_.GlobalTheory.BigOn.AtPtsAlt at hR
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at hC hN ⊢
  refine ((hR.and hC).and hN).imp fun Fm CH _ H => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := H
  obtain ⟨x0, hE⟩ := (h1.and h2).and h3
  refine ⟨x0, fun x hx hle i p hp hM w hw j h hh w' hw' => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := hE x hx hle i p hp
  obtain ⟨θ, hθ⟩ := a1 hM _ hw j
  obtain ⟨hCh, hOk, hU, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hM.1
  have hS : GlobalTheory.TraceIncl.HidaSetting (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w)) :=
    ⟨hCh.lev, hCh.grp.red_L, hCh.fam.tie, hCh.models, hCh.thP, hU, ⟨_, ((fw2 p).hv₀ j _).1⟩, (hOk.lifts _ _).act,
      fun g0 κ κ' k1 k2 => GlobalTheory.VecInv.omega_lifts_vP (R2 p) hCh.lev hCh.models.inf hCh.thP.ωP hCh.thP.vP j _ g0 κ κ' k1 k2⟩
  obtain ⟨y, -, hy⟩ := exists_adForm_levelTrace hS (a3 hM w hw j) (a2 hM w hw j) hθ hh hw'
  refine ⟨y, ?_, hy⟩
  obtain ⟨n, b, hbK, -, -, -, hsp⟩ := (fw2 p).ks j
  have hy0 := hsp.symm ▸ (Submodule.mem_top (x := y))
  refine Submodule.span_le.2 ?_ hy0
  rintro _ ⟨k, rfl⟩
  have hk : (p.nexp.fi j).e ((p.nexp.fi j).e.symm (b k)) = b k := (p.nexp.fi j).e.apply_symm_apply (b k)
  refine Submodule.subset_span ⟨(p.nexp.fi j).e.symm (b k), ((p.nexp.fi j).wk _).2 ?_, hk⟩
  first
    | exact hk.symm ▸ hbK k
    | exact (congrArg (fun z => z ∈ (p.R.FW j).WK) hk).mpr (hbK k)
    | (rw [hk]; exact hbK k)
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelTracedSeriesRationalStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adForm_eq_levelTrace_singleSeries : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ h ∈ GfC (Vc (Fm.D x i) j), ∀ w' : ((R2 p).cV j).W, InCoefLat (R2 p) j h w' →
  ∃ y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)), ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j y (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) h w' v) := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.adForm_eq_levelTrace_singleSeries' | exact _root_.GlobalTheory.BigOn.Exp.adForm_eq_levelTrace_singleSeries' | (intros; apply _root_.GlobalTheory.BigOn.Exp.adForm_eq_levelTrace_singleSeries' <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DescentOfReading
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DescentOfReading
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.Exp
section Generic
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}
variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end Generic
set_option maxHeartbeats 4000000 in
theorem descent_of_reading_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν rd => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w))
    (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL), (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) z = ∑ k, a k • rd (y k) := by
  unfold _root_.GlobalTheory.BigOn.Exp.CanonicalFits _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν rd hfit hcan => ?_⟩⟩⟩
  intro e he1 he2 z n a y hy hz
  have hν : ν ≠ 0 := hfit.2.1.1
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hRinj : Function.Injective R := readExt_injective _ e hL hF
  have hinc : ∀ z, R (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w)
      ((Fm.ex x hx i).nch.k' w) z) = rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
    | tmul c f =>
      rw [rdK_tmul, ← he2]
      rfl
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add (f := _), map_add (f := _)]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  apply hRinj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hinc, hz, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← algebraMap_smul (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k) (rd (y k)), hRdef, readExt_smul, ← hRdef,
    hrd _ (hy k), mul_smul]
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DescentOfReadingStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_embedding_compatible_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν rd => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w))
    (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL), (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) z = ∑ k, a k • rd (y k) := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.descent_of_reading_alt | exact _root_.GlobalTheory.BigOn.Exp.descent_of_reading_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.descent_of_reading_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScalarOfReading
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScalarOfReading
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn.Exp
section ScalarGeneric
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}
variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end ScalarGeneric
set_option maxHeartbeats 4000000 in
theorem scalar_of_reading_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL) (κ : ℂ) (N : ℕ),
    (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) → IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) → (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    ∃ b : (Fm.ex x hx i).nch.Oe w, rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
  unfold _root_.GlobalTheory.BigOn.Exp.CanonicalFits _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν rd hfit hcan => ?_⟩⟩⟩
  intro e he1 he2 z n a y κ N hy hN hint hz
  have hν : ν ≠ 0 := hfit.2.1.1
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hRinj : Function.Injective R := readExt_injective _ e hL hF
  have hinc : ∀ z, R (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w)
      ((Fm.ex x hx i).nch.k' w) z) = rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
    | tmul c f =>
      rw [rdK_tmul, ← he2]
      rfl
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add (f := _), map_add (f := _)]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  have hS : R (∑ k, a k • rd (y k)) = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k) (rd (y k)), hRdef, readExt_smul, ← hRdef,
      hrd _ (hy k), mul_smul]
  have hRHS : ∀ b : ((Fm.ex x hx i).nch.Oe w), ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) b) •
      ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun b => by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, smul_smul, mul_assoc]
  by_cases hT0 : ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0
  · exact ⟨0, by rw [hRHS, hz, hT0, smul_zero, smul_zero]⟩
  · obtain ⟨b₀, hb₀⟩ := readExt_scalar_mem_range _ e hL hF
      (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) z)
      (∑ k, a k • rd (y k)) κ (by rw [hinc, hS, hz]) (by rwa [hS])
    obtain ⟨m, hmI⟩ := hint
    obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_isIntegral e b₀ N hN m (by rwa [hb₀])
    exact ⟨b, by rw [hRHS, hz, hb, hb₀]⟩
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScalarOfReadingStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_ext_zero_product_vacuum_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL) (κ : ℂ) (N : ℕ),
    (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) → IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) → (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    ∃ b : (Fm.ex x hx i).nch.Oe w, rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.scalar_of_reading_alt | exact _root_.GlobalTheory.BigOn.Exp.scalar_of_reading_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.scalar_of_reading_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem twGe_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistLowerBound := by
  intro h1 h2 h3 h4 hA hC
  have h4' := GlobalTheory.SerStdFit.seriesRat_of_seriesRatS h4
  have hD := _root_.GlobalTheory.T.realization_embedding_compatible_alt
  have hR := _root_.GlobalTheory.T.adForm_eq_levelTrace_singleSeries h1 h2 h3 h4'
  have hG := _root_.GlobalTheory.T.twisted_embedding_compatibility_rows_alt h1 h2 h3 h4' hA hC
  have hS := _root_.GlobalTheory.T.schroedinger_ext_zero_product_vacuum_alt
  unfold _root_.GlobalTheory.BigOn.Exp.TwistLowerBound
  unfold _root_.GlobalTheory.BigOn.Exp.CanonicalFits _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at hD hG hS ⊢
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at hR
  refine (((hD.and hR).and hG).and hS).imp fun Fm CH _ H => ?_
  obtain ⟨x0, hx0⟩ := ((H.1.1.1.and H.1.1.2).and H.1.2).and H.2
  refine ⟨x0, fun x hx h0 i p hp hM w hw j ρ hρ ν rd hfit hcan => ?_⟩
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hx0 x hx h0 i p hp
  have d := k1 hM w hw j ρ hρ ν rd hfit hcan
  have r := k2 hM w hw j
  have g := k3 hM w hw j ρ hρ ν rd hfit hcan
  have s := k4 hM w hw j ρ hρ ν rd hfit hcan
  obtain ⟨-, e, he1, he2⟩ := hfit.1
  unfold twLat
  refine Submodule.span_le.2 ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, h, w', a, κ, N, hN, hκ, hhw, ha⟩ := g e he1 he2 z hz
  choose y hy hyv using fun k => r (h k) (hhw k).1 (w' k) (hhw k).2
  obtain ⟨b, hb⟩ := s e he1 he2 z n a y κ N hy hN hκ (ha y hyv)
  rw [d e he1 he2 z n (fun k => b * a k) y hy hb]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y k,
    Submodule.subset_span ⟨h k, (hhw k).1, w' k, (hhw k).2, fun v => ?_⟩, rfl⟩)
  rw [one_smul]
  exact hyv k v
end GlobalTheory.BigOn.Exp
end
