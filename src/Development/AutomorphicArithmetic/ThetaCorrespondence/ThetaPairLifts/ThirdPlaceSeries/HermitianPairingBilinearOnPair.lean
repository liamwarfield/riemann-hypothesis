module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValuationMultiplicityOfConsecutiveRun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionality

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermitianPairingBilinearOnPair
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
theorem birOn_u₁_u₂_alt_alt : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ∧ BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂ 0) := by
  intro hX hG hQ hSi hP2 hS
  have hP := _root_.GlobalTheory.T.covering_topology_refinement hP2
  have hBir : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q →
      ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)),
      (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 →
        (((CompHt.dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) →
      ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) :=
    _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hSi hP hP2.q15 hP2.q16
  refine Closed.imp (((_root_.GlobalTheory.T.size_bounds_for_family_alt hS).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS)).and _root_.GlobalTheory.HSApp.wtBig_run_alt) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, H1⟩, ⟨C2, -, H2⟩⟩, ⟨C3, -, H3⟩⟩
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, H⟩ := (H1.and H2).and H3
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := H x hx hle ι p hp
  have s1 := a1 i hi Y hY
  have s2 := a2 i hi
  have hB := a3 i hi
  intro Z
  have G := gaps_u₁_u₂_of_wtBig _ hB
  exact ⟨hBir (Fm.D x ι) p.T s1.1 ((i : ℕ) + 1) s2.1 s2.2.1 Y _ _ hY.1 _ (fun τ a b h => (G τ a b h).1) Z,
    hBir (Fm.D x ι) p.T s1.1 ((i : ℕ) + 1) s2.1 s2.2.1 Y _ _ hY.1 _ (fun τ a b h => (G τ a b h).2) Z⟩
end GlobalTheory.HSApp
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birOn_weightPair_both_components_alt : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ∧ BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂ 0) := by
  first | exact @_root_.GlobalTheory.HSApp.birOn_u₁_u₂_alt_alt | exact _root_.GlobalTheory.HSApp.birOn_u₁_u₂_alt_alt | (intros; apply _root_.GlobalTheory.HSApp.birOn_u₁_u₂_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkOfBuilt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TwInputs.JoinModel
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
section General
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop}
variable {G : Type} [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} {S : RatDat D.ntw}
  {YS : NExpRealS R cG S} {cf : CharFrame D}
end General
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
variable {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch} {xd : ThData (w.D Z)} {c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n}
def twistInputsOfBaseTuples {hH hV hs} (Y : SerSide (realOf t hH hV hs) (twEOf xd))
    (hS : Y.S = ratDatR t.r.z.R t.r.z.cG c.row.kKs c.row.hk) (hY : HEq Y.YS c.row.nexp) (g : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7)
    (h1 : g.cf = TC.cf w.I w.l Z) (h2 : g.lam.C = TC.cf w.I w.l Z) (hF : FieldOk (realOf t hH hV hs))
    (cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (w.st Z).toD7 g.wd)
    (hb : T = TwDat.untw B T.pl → ∀ v, (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 → BaseTup Y (nch.twI v)) :
    _root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c :=
  ⟨realOf t hH hV hs, rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, Y, hS, hY, g,
    h1, h2, t.r.z.lev.C, hF, cg, hb⟩
def heckeSeriesOfRealHeight {hH hV hs} (e : _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)
    (H : NExpRealH t.r.z.R t.r.z.cG _ c.row.nexp) (hr : GlobalTheory.ExportPin.Reads t.r.z.R t.r.z.cG _ c.row.nexp H.hL)
    (hd : ∀ i b P, P ∉ (w.D Z).ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G (w.D Z).host.E (w.D Z).nd.Om,
      Formalism.ConjugateSelfDual.IsFrob (F := (w.D Z).host.E) ((w.D Z).nd.plOm.1 P) (Formalism.ConjugateSelfDual.normV P) σ →
      H.cHk i b 1 P = algebraMap ((w.D Z).ntw.O i) (FractionRing ((w.D Z).ntw.O i)) (algebraMap ((w.D Z).ntw.O0 i) ((w.D Z).ntw.O i)
        ((if b then (w.D Z).ntw.delta i σ else ((w.D Z).ntw.delta i σ)⁻¹ : ((w.D Z).ntw.O0 i)ˣ) : (w.D Z).ntw.O0 i)))
    (hk_emb : ∀ i j b k P (x : (w.D Z).ntw.B i j b), 1 ≤ j → j ≤ B.R.m → IntegralHeckeForms.HkIdx i k P →
      (w.D Z).nexp.embB i j b ((w.D Z).ntw.hk i j b k P x) = (w.D Z).nexp.hkF i j b k P ((w.D Z).nexp.embB i j b x))
    (hz : ∀ i (s : (w.D Z).ntw.Sig i) P, (w.D Z).ntw.hEig i s 0 P = 1) : SerSide (realOf t hH hV hs) (twEOf xd) where
  S := _
  YS := c.row.nexp
  sup := e.ser.sup
  H := H
  reads := hr
  del := hd
  Z := e.ser.ex
  U_eq g := (c.row.grp.lvl0 g).symm
  psi_eq := psi_of_grp c.row.grp e.ser.ex
  low := low_of_tied c.a.all.tw (q_dvd_discr _)
  Sb i P hP := by
    have hA : t.r.z.R.Sb = t.r.z.R.Pg := t.r.z.pins.char.allPl
    obtain ⟨k, hk⟩ := e.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true P
      (by rw [e.ser.ex.pin.Pg]; exact hA ▸ hP)
    exact (w.D Z).ntw.placesOver_subset_exceptional i k hk
  B_range i _ j _ b := c.a.all.tw.B_range i j b
  hk_emb := hk_emb
  hk_split i _ j _ b k P h := by
    obtain ⟨s, hs⟩ := c.a.all.tw.hk_split i j b k P h.2.2.2
    exact hs ▸ Polynomial.Splits.multisetProd fun p hp => by
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hp
      exact Polynomial.Splits.X_sub_C a
  off i _ := ⟨fun j hj b => e.ser.off i j b fun h => hj (Finset.mem_Icc.2 h), hz i⟩
  all i j hj b a := by
    have := e.xd i j b (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
    change a ∈ xd.xd0 i j b
    rw [this]; trivial
theorem exists_wdTie_cgTrue_labTrue_of_built {D : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) :
    ∃ wd : GlobalTheory.RowTie.WDTie D.nd D.naut, Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D wd) ∧ LabTrue D wd := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  exact ⟨{ A.wdT with }, ⟨{ cg with }⟩, A.lab⟩
theorem exists_galSide_of_rank_ge_hundred (e : _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) (h3 : _root_.GlobalTheory.Triple.IsGaloisTriple (w.D Z)) (hr : 100 ≤ B.R.r)
    (hg : ∀ k, 2 * B.R.r ≤ B.host.g k) : ∃ g : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, g.cf = TC.cf w.I w.l Z ∧ g.lam.C = TC.cf w.I w.l Z ∧
      Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL (w.st Z).toD7 g.wd) := by
  obtain ⟨wd, cg, lab⟩ := _root_.GlobalTheory.TwInputs.JoinModel.exists_wdTie_cgTrue_labTrue_of_built c.a.nt.toNBuilt
  exact ⟨⟨wd, lab, TC.cf w.I w.l Z, { c.a.chrN with }, h3, e.ser.lam, e.ser.lam_ok, fun i hi => (e.ser.lam_tie i hi).imp id (Exists.imp fun _ h => ⟨h.1, h.2.1⟩), hr, hg⟩, rfl, e.ser.lam_C, cg⟩
theorem embB_hk_commute_and_hEig_zero_of_built {D : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) :
    (∀ i j s k P (x : D.ntw.B i j s), 1 ≤ j → j ≤ D.R.m → IntegralHeckeForms.HkIdx i k P →
      D.nexp.embB i j s (D.ntw.hk i j s k P x) = D.nexp.hkF i j s k P (D.nexp.embB i j s x)) ∧
    ∀ i (s : D.ntw.Sig i) P, D.ntw.hEig i s 0 P = 1 := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  exact ⟨fun i j s k P x h1 h2 h => Bs.hk_emb i j s k P x h1 h2 h.2.2.2 h.2.2.1 h.2.1, Bs.hEig_zero⟩
end Rows
end GlobalTheory.TwInputs.JoinModel
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SatakeIdentityOfIsTriple
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Triple
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open _root_.Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)
variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}
variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {s : X.Sig i}
section With
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : Zbar (X.l i) →+* FbAt D w}
theorem IsGaloisTripleWithReduction.unrRho {b : Bool} {ρ : Reading X i b} (ha : IsGlobalArtin art)
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) : UnrRho i s := by
  intro v hl hg A hA g hgI
  obtain ⟨n, hn⟩ := h.shift
  have e := h.rho g
  rw [_root_.GlobalTheory.Triple.unramified_of_isGaloisRepOfN_of_unr h.gal hl (h.param.unr v hg) hA hgI,
    (hn.unr_iff ha (Or.inl hl) hA).2 (shiftChar_unr C v) g hgI, Units.val_one, map_one, one_smul, Units.val_one] at e
  refine Units.ext (Matrix.map_injective (GlobalTheory.GalChar.toQ_injective ρ.κ) ?_)
  simpa using e
theorem IsGaloisTripleWithReduction.charpolyRev_matW {ρ : Reading X i (X.side i s)} (ha : IsGlobalArtin art) (hC : IsChars C art ρ)
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) {P : PlE D.host} (hS : P ∉ X.S0 i) {B : ValuationSubring D.nd.Om}
    (hB : IsPlaceOver (F := D.host.E) B P) {g : GalE D} (hF : IsFrob (F := D.host.E) B (normV P) g⁻¹) :
    (matW s g).charpolyRev.map ρ.toC = ((satake (muBase C (X.l i) (jIdx s)) π P).map fun α =>
      1 - Polynomial.C (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2) * α) * Polynomial.X).prod := by
  have hl : P ∉ placesOver D.host.E (X.l i) := fun hk => hS (X.twistExcludedPlaces_contains_residueChar i hk)
  have hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS (X.placesOver_subset_exceptional i k hk)
  obtain ⟨n, hn⟩ := hC.chiS
  have hu := (hn.unr_iff ha (Or.inl hl) hB).1 (X.twistCharacterFamily_unramified i _ _ P hl hg (fun hk => hS (X.primes_subset_exceptional i hk)) B hB)
  have e1 := h.charpoly_frob ha hl hg hB hF
  have e2 : ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i) =
      (((blockChar C (X.l i) (jIdx s)).val P : ℂˣ) : ℂ) * ((normV P : ℕ) : ℂ) ^ D.R.t := by
    rw [twistW, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_pow_eq_pow_val,
      cyclotomicEps_frobenius_eq_norm hl hB hF, map_mul, map_pow, map_natCast, map_units_inv, ρ.toC_apply,
      hn.frob ha (Or.inl hl) hu hB hF, inv_inv, mul_comm]
  rw [← Matrix.charpoly_map, ← Function.comp_def (fun a => Polynomial.X - Polynomial.C a), ← Multiset.map_map] at e1
  have e3 := charpoly_smul_of_prod _ _ (ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i)) e1
  have e4 : (matW s g⁻¹).map ρ.toC = ρ.toC ((twistW s g⁻¹ : (X.O0 i)ˣ) : X.O0 i) •
      ((X.rhoS i s g⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map ρ.toC := by
    ext x y
    simp [matW]
  rw [← e4, ← Function.comp_def (fun a => Polynomial.X - Polynomial.C a), ← Multiset.map_map] at e3
  have e5 : (matW s g).map ρ.toC * (matW s g⁻¹).map ρ.toC = 1 := by
    rw [← Matrix.map_mul, matW_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [charpolyRev_map, charpolyRev_of_inv e5 e3, satake, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [← geometric_eigenvalue, e2, ← mul_assoc]
theorem IsGaloisTripleWithReduction.hkFrob {ρ : Reading X i (X.side i s)} (ha : IsGlobalArtin art) (hC : IsChars C art ρ)
    (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) : HkFrob i s := by
  intro P hS hP g hF k hk
  obtain ⟨x, h1, h2⟩ := h.hecke k P hk hP hS
  have e := congrArg (fun (p : ℂ[X]) => p.coeff k) (h.charpolyRev_matW ha hC hS (D.nd.plOm.2 P) hF)
  simp only [coeff_map, GlobalTheory.coeff_prod_one_sub_C_mul_X] at e
  have e2 : ((normV P : ℕ) : ℂ) ^ (k * (k - 1) / 2) * heckeVal (muBase C (X.l i) (jIdx s)) π k P =
      (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2)) ^ k * (satake (muBase C (X.l i) (jIdx s)) π P).esymm k :=
    (pow_mul_heckeVal _ π P hk).trans
      (Multiset.pow_smul_esymm (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2)) k (satake (muBase C (X.l i) (jIdx s)) π P)).symm
  have e3 : (-1) ^ k * ((normV P : ℕ) : X.O0 i) ^ (k * (k - 1) / 2) * x = (matW s g).charpolyRev.coeff k := by
    apply ρ.toC_injective
    rw [e, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast, h2, mul_assoc, e2, mul_assoc]
  rw [← matW_eq, ← e3, ← h1, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast]
end With
variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}
theorem IsGaloisTripleOfExpansion.unrRho (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) (hi : X.NonzeroIndexPlace i) (s : X.Sig i) : UnrRho i s :=
  let ⟨_, _, h⟩ := h
  let ⟨_, _, _, _, _, _, _, _, h2⟩ := h.triple hi s
  h2.unrRho h.artin
theorem IsGaloisTripleOfExpansion.hkFrob (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) (hi : X.NonzeroIndexPlace i) (s : X.Sig i) : HkFrob i s :=
  let ⟨_, _, h⟩ := h
  let ⟨_, h1, _, _, _, _, _, _, h2⟩ := h.triple hi s
  h2.hkFrob h.artin h1
theorem IsGaloisTripleOfExpansion.adm8 (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) : adm8 X Y := by
  intro i hi s _
  have hu := h.unrRho hi s
  refine ⟨twistW s, ?_, fun P hS _ A hA g hI => ?_, fun v hv A hA => ?_, fun P hS hP g hF => ?_⟩
  · obtain ⟨ρ⟩ := Reading.nonempty i true
    exact Units.continuous_val.comp
      (((GlobalTheory.GalChar.continuous_units _ (GlobalTheory.GalChar.continuous_cyc (X.twistBaseCoefficientRing_isAdic i) ρ.κ_alg)).pow D.R.t).mul
        (GlobalTheory.GalChar.continuous_units _ (X.twistCharacterFamily_continuous i _ _)).inv)
  · have hl : P ∉ placesOver D.host.E (X.l i) := fun hk => hS (X.twistExcludedPlaces_contains_residueChar i hk)
    have hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hS (X.placesOver_subset_exceptional i k hk)
    refine (matW_of_mem_Ine hu hl hg hA hI).trans ?_
    rw [chiS, X.twistCharacterFamily_unramified i _ _ P hl hg (fun hk => hS (X.primes_subset_exceptional i hk)) A hA g hI, inv_one, Units.val_one, one_smul]
  · obtain ⟨hl, hg⟩ := notMem_of_mem_pD hv
    cases hb : X.side i s
    · refine Or.inl fun g hI => (matW_of_mem_Ine hu hl hg hA hI).trans ?_
      rw [chiS, X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA g hI, hb, if_neg Bool.false_ne_true, inv_inv]
    · refine Or.inr fun g hI => (matW_of_mem_Ine hu hl hg hA hI).trans ?_
      rw [chiS, X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA g hI, hb, if_pos rfl]
  · change _ = algebraMap (X.O0 i) (X.O i) (1 - matW s g).det
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_coeff_charpolyRev, map_sum, matW_eq]
    exact Finset.sum_congr rfl fun k hk => h.hkFrob hi s P hS hP g hF k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
theorem adm8_allGood_sig_of_isTriple (D : D7) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D) :
    Formalism.MainNotions.BlochKatoReduction.Gen.adm8 D.ntw D.nexp ∧ GlobalTheory.TwSys.AllGood D.nexp ∧ D.nexp.sig_all :=
  ⟨_root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.adm8 h, _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.allGood h, _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.sig_all h⟩
end GlobalTheory.Triple
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringDegreeMultiplicative
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
namespace GlobalTheory.CovTop.DegProof
set_option maxHeartbeats 1000000 in
theorem covering_degree_eq_alt : HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation →
    GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree := by
  intro hX h2 hS hT hG hQ hN hDG hSz hF
  have hP := _root_.GlobalTheory.T.covering_topology_refinement h2
  refine Closed.imp (Closed.and (Closed.and (_root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt h2 hG hQ hS hT hN hDG hSz hF) _root_.GlobalTheory.HSApp.wtBig_run_alt)
    (Closed.and (Closed.and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz) (_root_.GlobalTheory.T.size_bounds_for_family_alt hSz)) hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨⟨_, -, a₃⟩, _, -, a₄⟩, _, -, a₅⟩
  obtain ⟨x0, a⟩ := (a₁.and a₂).and ((a₃.and a₄).and a₅)
  clear a₁ a₂ a₃ a₄ a₅
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩, a₅⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨hp1, hq1, hE, hQuo, hAnti, -, -⟩ := a₃ i hi
  obtain ⟨hLaw, hIn, -⟩ := a₄ i hi Y hY
  obtain ⟨-, -, -, -, -, -, ⟨Z'⟩, -⟩ := a₅ i hi Y hY
  have hW := a₂ i hi
  have hV := a₁ i hi Y hY
  rw [hQuo u1 hu1]
  have hPr := _root_.GlobalTheory.T.proportionality_principle_compactification h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hEq := _root_.GlobalTheory.T.compactification_top_chern_eq_volume h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hBir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hS hP h2.q15 h2.q16 _ p.T hLaw _ hp1 hq1 Y _ _ hY.1 _ (fun τ a b hab => by
    have hb := b.2
    have h := hW.gaps τ a (by rw [← hab]; exact hb)
    rw [gap_eq _ hab] at h
    refine le_trans ?_ h
    have e : ∀ d C N : ℕ, (d + 3) ^ 2 + 2 * N ≤ (d + 3) * (C + 4 * N + d + 3) := fun d C N => by nlinarith
    rw [GlobalTheory.CompHS.dimFlag_eq]
    exact_mod_cast e _ _ _)
  have key := GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.1.unf hPr.1 hEq _ (fun τ => (hAnti τ).1) (fun τ => (hAnti τ).2) hBir hV
  refine ⟨CompHt.delPrime Y.U Z' _, ?_, fun Z => key Z Z'⟩
  exact mul_pos (hPr.2 Z') (Int.cast_pos.2 (CompHt.vdm_pos fun τ => (hAnti τ).2))
end GlobalTheory.CovTop.DegProof
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverDegree_of_grothendieck_deformation : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree := by
  first | exact @_root_.GlobalTheory.CovTop.DegProof.covering_degree_eq_alt | exact _root_.GlobalTheory.CovTop.DegProof.covering_degree_eq_alt | (intros; apply _root_.GlobalTheory.CovTop.DegProof.covering_degree_eq_alt <;> assumption)
end
end
end
