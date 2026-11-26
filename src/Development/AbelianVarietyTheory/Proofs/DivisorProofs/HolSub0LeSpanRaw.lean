module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockEmb
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationTranslation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
section -- merged from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.InducedEqOne
noncomputable section

namespace GlobalTheory.DeltaPinTest

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem noDelta_phiPin (nab : NabV Xo c) (m : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (noDelta Xo c nab m n).PhiPin (fun _ => 1) 1 (fun _ => 0) := by
  haveI hs : Subsingleton (LaJ Xo c (noDelta Xo c nab m n)) := by
    apply Submodule.Quotient.subsingleton_iff.2
    show Ideal.map _ ⊤ • ⊤ = ⊤
    rw [Ideal.map_top, Submodule.top_smul]
  refine ⟨fun _ _ _ => rfl, fun _ _ => Subsingleton.elim _ _, fun _ _ _ _ => by simp, rfl,
    Subsingleton.elim _ _, fun q => ?_⟩
  haveI : Unique (Fin n → LaJ Xo c (noDelta Xo c nab m n)) := uniqueOfSubsingleton (fun _ => 0)
  rw [finsum_unique]
  have hz : ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) = 1 := by
    have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    apply Subtype.ext
    rw [Nat.div_one]
    exact (Complex.isPrimitiveRoot_exp _ h0).pow_eq_one
  show (noDelta Xo c nab m n).eF 1 = (noDelta Xo c nab m n).eF 1 * ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) ^ _
  rw [hz]
  exact ((congrArg _ (one_zpow _)).trans (mul_one _)).symm

end GlobalTheory.DeltaPinTest
end
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RawSpan

section Cover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev idCover (nab : NabV Xo c) (n : ℕ) : DeltaDat Xo c n := noDelta Xo c nab (GlobalTheory.ObjLower.sabId Xo.univ.t) n

theorem frOver_self (nab : NabV Xo c) (n : ℕ) {S : Type} [CommRing S] [i : Algebra c.F S] (y : FrPt Xo c S) :
    @FrOver E _ _ _ H Dw l Xo c n (idCover nab n) S _ i i y y := by
  refine (@GlobalTheory.FrameLift.frOver_iff E _ _ _ H Dw l Xo S _ c n (idCover nab n) i i y y).2
    ⟨Category.comp_id _, fun _ _ => Category.comp_id _, GlobalTheory.ObjLower.idIso Xo.univ.t.PP.L, 𝟙 _,
      ⟨(isGen_iff _).2 (GlobalTheory.ObjLower.pgen_idIso Xo.univ.t.PP.isLB), ?_⟩,
      (Category.id_comp _).trans (Category.comp_id _).symm, Category.id_comp _, ?_⟩
  · exact (maps_iff (GlobalTheory.ObjLower.idIso Xo.univ.t.PP.L) _ (fun _ => eSec Xo.univ.t.G) _ Xo.univ.t.PP.rig
      Xo.univ.t.PP.rig (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e _
      (rigPull_le (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).F (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e
        (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e_comm Xo.univ.t.PP.L) (fun _ => rfl)).2
      (GlobalTheory.ObjLower.pmaps_idIso _ _ _ _ Xo.univ.t.PP.rigGen)
  · intro Z r z i j hi hj
    have e := GlobalTheory.ObjLower.gw_idIso Xo.univ.t.PP.L (r ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) z i j hi hj
    have e' := GlobalTheory.FrameLift.sv_trans (q := (snd (Over.mk y.x) Xo.univ.t.G).left) y.s r z hi hj
    exact (congrArg (fun t => GlobalTheory.FrameLift.sv (q := (snd (Over.mk y.x) Xo.univ.t.G).left) y.s t z i)
      (Category.comp_id r)).trans (e'.trans (congrArg (fun u : (Z.presheaf.stalk z)ˣ => u.val * _) e.symm))

theorem evR_one_field (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) : evR Xo c 1 y = 1 :=
  evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)

theorem idCover_isLev (nab : NabV Xo c) (n : ℕ) : (idCover nab n).IsLev := by
  refine ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, (Nat.mul_one _).symm, Nat.coprime_one_left _, (Ideal.mul_top _).symm,
    top_sup_eq _, ?_, ?_, GlobalTheory.LevelCover.one_mem_sec_zero Xo c, ?_⟩
  · rw [GlobalTheory.LevelCoverDatum.noDelta_etaOK]
    exact ⟨fun a => Category.comp_id _, fun a => Category.comp_id _⟩
  · intro k _ _ i₁ i₂ hk y
    have e : i₂ = i₁ := Algebra.algebra_ext _ _ fun a => hk a
    rw [e]
    exact ⟨y, @frOver_self E _ _ _ H Dw l Xo c nab n k _ i₁ y⟩
  · intro k _ _ i y₂
    have := @evR_one_field E _ _ _ H Dw l Xo c k _ i y₂
    exact fun h => one_ne_zero (this.symm.trans h)

theorem idCover_unitC (nab : NabV Xo c) (n : ℕ) : GlobalTheory.Dict.UnitC (idCover nab n) := fun A y =>
  (congrArg norm (@evR_one_field E _ _ _ H Dw l Xo c ℂ _ A y)).trans norm_one

theorem idCover_psiTie (nab : NabV Xo c) (n : ℕ) : (idCover nab n).PsiTie 1 := by
  intro k g ρ _ _ _ _ K _ _ i y y' _
  have a := @evR_one_field E _ _ _ H Dw l Xo c K _ i y
  have b := @evR_one_field E _ _ _ H Dw l Xo c K _ i y'
  refine b.trans ?_
  refine Eq.symm ((congrArg _ a).trans ?_)
  simp

theorem betaH_ne_zero {n : ℕ} (Λ : GenLat E n) : betaH (Dw := Dw) c Λ ≠ 0 := by
  unfold betaH
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem phiHat_indPhi_mk {n : ℕ} (x0 : Fin n → Dw.La) :
    phiHat c (indPhi c fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) = x0Dat c x0 := by
  have h : phiHat c (indPhi c fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) =
      x0Dat c fun b => qRep (Submodule.Quotient.mk (x0 b) : LevQc Dw l) := by
    funext q
    unfold phiHat x0Dat indPhi
    rw [finsum_eq_single _ (fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) (fun x hx => by simp [hx])]
    simp
  rw [h, GlobalTheory.LevelPairing.levelFourierDatum_eq_iff]
  intro b
  exact (Submodule.Quotient.eq _).1 (Classical.choose_spec (Submodule.Quotient.mk_surjective _
    (Submodule.Quotient.mk (x0 b) : LevQc Dw l)))

theorem span_mk_eq_top {n : ℕ} (x0 : Fin n → Dw.La) (h : AdmX (l := l) true x0) :
    Submodule.span (𝓞 E) (Set.range fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) = ⊤ := by
  unfold AdmX at h
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, Set.image_image] at h
  rw [← h]
  congr 1
  ext z
  simp

theorem thLaValAt_of_isShortRule [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) {n : ℕ} {Λ : GenLat E n} {N : ℕ}
    (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M) {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) (x0 : Fin n → Dw.La) {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (h : IsShortRule Xo c (idCover nab n) Λ N x0 P f) (p : TRing c.F) (y : FrPt Xo c p.R) :
    thLaValAt Xo c nab (x0Dat c x0) Λ N P y ((betaH (Dw := Dw) c Λ • f) p y) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 (x0Dat c x0) (betaH (Dw := Dw) c Λ)
  obtain ⟨v, hv, -⟩ := hval p.R y
  have e : f p y = v := by
    refine GlobalTheory.CoverDescent.eq_of_geometric_points _ _ fun k _ _ χ => ?_
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χa y
    obtain ⟨u, hu, eu⟩ := @h k _ _ i1 i1 (fun _ => rfl) z z (frOver_self nab n z)
    have hu' : ShortValAt Xo c nab (x0Dat c x0) Λ (betaH (Dw := Dw) c Λ) N P z u := by
      have e1 : MvPolynomial.map ((idCover nab n).eF : c.F →+* (idCover nab n).c₂.F) P = P := MvPolynomial.map_id P
      rw [e1, GlobalTheory.LevelCoverDatum.noDelta_w] at hu
      exact hu
    have e2 := hnat p.R k χa y z hz v u hv hu'
    have e3 := GlobalTheory.CoverDescent.evR_of_test (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1 f hf.1
      p χa y z hz
    have e4 : evR Xo c f z = u := eu.trans ((congrArg (· * u) (evR_one_field k z)).trans (_root_.one_mul u))
    exact e3.symm.trans (e4.trans e2.symm)
  have e5 : (betaH (Dw := Dw) c Λ • f) p y = algebraMap c.F p.R (betaH (Dw := Dw) c Λ) * v := by
    rw [← e]
    exact Algebra.smul_def (betaH (Dw := Dw) c Λ) (f p y)
  rw [e5]
  exact (GlobalTheory.Survey.BaseClassMove.shortValAt_beta Xo c nab _ Λ _ (betaH_ne_zero Λ) N P y v).1 hv

end Cover

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor


set_option maxHeartbeats 1000000 in
theorem holSub0_le_span_raw : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c σ r), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) l.M) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (bad n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, GlobalTheory.Dict.ChiOne (U.X k) (Formalism.L2.Pj.laU U a n k)) → Formalism.L2.Pj.holSub0 U.X (Formalism.L2.Pj.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.Pj.rdU U '' ⋃ (x0 : Fin n → LevQc Dw l) (_ : Submodule.span (𝓞 E) (Set.range x0) = ⊤), {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)}) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr hA hG hP _ nab hnab bad n a hbad hdom hn hχ
  have hC := GlobalTheory.chartIndependence_unconditional
  have hrk : r = Dw.p + Dw.q := hU.1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hpin := GlobalTheory.DeltaPinTest.noDelta_phiPin (n := n) nab (GlobalTheory.ObjLower.sabId Xo.univ.t)
  have hT := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have hW := (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1
  have htot : ShortValTot Xo c nab bad n a n (idCover nab n) :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n (idCover nab n) (GlobalTheory.levelMaps_closed hL E H Dw h1) hW hT hW hT
      (idCover_isLev nab n) rfl ⟨_, hnab⟩ (fun _ => ⟨_, 1, _, hpin, idCover_psiTie nab n⟩) nab bad n a
  have key := GlobalTheory.Dict.holSub0_le_span_shortGen hC E H Dw l Xo c n (idCover nab n) σ r
    (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr hA hG hP (idCover_isLev nab n) ⟨_, hnab⟩ (idCover_unitC nab n)
    (by show ¬ 3 ∣ 1; decide) (fun _ => ⟨_, 1, _, hpin⟩) nab bad n a hbad hdom hn hχ htot
  intro Q hQ
  refine Submodule.span_le.2 ?_ (key hQ)
  rintro _ ⟨f, ⟨hf, Λ, N, x0, P, hΛ, hb, hM, hO, hX, hPm, hrule⟩, rfl⟩
  have hβ := betaH_ne_zero (Dw := Dw) (c := c) Λ
  have e : Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj U) f =
      (σ (betaH (Dw := Dw) c Λ))⁻¹ • Formalism.L2.Pj.rdU U (betaH (Dw := Dw) c Λ • f) := by
    rw [LinearMap.map_smulₛₗ, smul_smul, inv_mul_cancel₀ ((map_ne_zero σ).2 hβ), one_smul]
    rfl
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
  rw [decide_eq_true (rfl : n = n)] at hX
  refine Set.mem_iUnion₂.2 ⟨fun b => Submodule.Quotient.mk (x0 b), span_mk_eq_top x0 hX,
    Submodule.smul_mem _ _ hf, Λ, N, P, hΛ, hb, hM, hO, hPm, fun p y => ?_⟩
  rw [phiHat_indPhi_mk]
  exact thLaValAt_of_isShortRule nab hnab hΛ hM hO hPm x0 hf hrule p y

end GlobalTheory.RawSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaSobolevBase

open scoped Classical SchwartzMap ENNReal

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F) in
def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evHom_invOf_two [Invertible (2 : AF F)] :
    evHom F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
  have h2 : evHom F (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evHom F) 2, ← map_mul, invOf_mul_self, map_one]
  calc evHom F (⅟(2 : AF F)) = evHom F (⅟(2 : AF F)) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (2 * (1 / 2)) := by
        rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, map_one, mul_one]
    _ = (evHom F (⅟(2 : AF F)) * 2) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
        rw [map_mul, map_ofNat]; ring
    _ = _ := by rw [h2, one_mul]

def sumPure {ι : Type} [Fintype ι] (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : ι → SInf F κ) : (κ → AF F) → ℂ :=
  ∑ i, pureA F (f i) (g i)

theorem exists_sumPure {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (n : ℕ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin n → SInf F κ), (∀ i, g i ∈ SB _) ∧
      Φ = sumPure g f := by
  obtain ⟨n, c, p, hp⟩ := Submodule.mem_span_set'.1 hΦ
  choose f g hg he using fun i => (p i).2
  refine ⟨n, g, fun i => c i • f i, hg, ?_⟩
  rw [← hp, sumPure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he i, ← GlobalTheory.WeilAdm.pureA_smul]
  rfl

theorem memLp_pureA (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (f : SInf F κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB _) :
    MemLp (pureA F f g) 2 μ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  obtain ⟨ν, hν, C, c, hC, -, -, h, -⟩ := GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds F κ g hg ⊤ isOpen_univ
  have hc : Continuous (pureA F f g) := by
    have h1 := GlobalTheory.WeilAdm.HaarSplit.continuous_comp_splitE F κ (pureA F f g)
      (Submodule.subset_span ⟨f, g, hg, rfl⟩)
    have h2 := h1.comp (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)
    convert h2 using 1
    funext x
    simp
  have hf : ∫⁻ z, ‖f z‖ₑ ^ 2 < ⊤ := by
    have := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (p := 2)
      (by norm_num) (by norm_num) (f.memLp 2 volume)
    simpa using this
  have hν2 : MemLp (pureA F f g) 2 ν := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by norm_num) (by norm_num) hc.aestronglyMeasurable]
    have := (h f).trans_lt (ENNReal.mul_lt_top hC.lt_top hf)
    simpa using this
  rw [Measure.isAddLeftInvariant_eq_smul μ ν]
  exact hν2.smul_measure ENNReal.coe_ne_top

end GlobalTheory.ThetaSobolevBase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatVecDomain

theorem discrete_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    DiscreteTopology (GlobalTheory.ThetaParseval.ratVec F κ) := by
  obtain ⟨U, hU, hx⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have hN : (Set.univ.pi fun _ : κ => U) ∈ nhds (0 : κ → AdeleRing (𝓞 F) F) :=
    set_pi_mem_nhds Set.finite_univ fun _ _ => hU
  refine discreteTopology_of_isOpen_singleton_zero ?_
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
  have hc : ContinuousAt (fun x : GlobalTheory.ThetaParseval.ratVec F κ => (x : κ → AdeleRing (𝓞 F) F)) 0 :=
    continuous_subtype_val.continuousAt
  refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
  rintro ⟨y, hy⟩ hyU
  obtain ⟨ξ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff y).1 hy
  have hξ : ξ = 0 := funext fun i => hx _ (hyU i (Set.mem_univ i))
  subst hξ
  refine Subtype.ext ?_
  funext i
  simp

theorem exists_compact_cover_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ K : Set (κ → AdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ x, ∃ γ ∈ GlobalTheory.ThetaParseval.ratVec F κ, γ + x ∈ K := by
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  choose c hc using hx
  refine ⟨Set.univ.pi fun _ : κ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  refine ⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (-c (x i)),
    (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨fun i => -c (x i), rfl⟩, fun i _ => ?_⟩
  have := hc (x i)
  simpa [map_neg, neg_add_eq_sub] using this

theorem exists_fundamentalDomain : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ 𝓕₁ : Set (κ → AF F), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ ∧ μ 𝓕₁ ≠ 0 ∧ μ 𝓕₁ ≠ ⊤ := by
  intro F _ _ κ _ μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := discrete_ratVec F κ
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) :=
    GlobalTheory.countable_of_discrete_addSubgroup _
  obtain ⟨K, hK, hcov⟩ := exists_compact_cover_ratVec F κ
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup
    (GlobalTheory.ThetaParseval.ratVec F κ)
  exact ⟨D, hD μ, (hD μ).measure_ne_zero (NeZero.ne μ),
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov μ (hD μ)).ne⟩

end GlobalTheory.RatVecDomain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ 𝓕₁ : Set (κ → AF F), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ ∧ μ 𝓕₁ ≠ 0 ∧ μ 𝓕₁ ≠ ⊤ := by
  first | exact @GlobalTheory.RatVecDomain.exists_fundamentalDomain | exact GlobalTheory.RatVecDomain.exists_fundamentalDomain | (intros; apply GlobalTheory.RatVecDomain.exists_fundamentalDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductSchwartzGlue
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

namespace GlobalTheory.ThK.EvAt0.SchwartzProd


open scoped Classical in
theorem exists_prod : ∀ {F : Type} [Field F] [NumberField F] {n d d₁ : ℕ} (h : d = d₁ + 2) (G : SInf F (Fin n × Fin 2))
    (f : SInf F (Fin n × Fin d₁)), ∃ g : SInf F (Fin n × Fin d), ∀ y,
      g y = G (fun p => y ((idx h).symm (Sum.inr p))) * f (fun q => y ((idx h).symm (Sum.inl q))) := by
  intro F _ _ n d d₁ h G f
  obtain ⟨b, hb⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box f G
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n × Fin d => mixedEmbedding.mixedSpace F)
      (idx h).symm).symm b, fun y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hb, mul_comm]
  rfl

end GlobalTheory.ThK.EvAt0.SchwartzProd
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvAt0.PolEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Gen

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem at_symm (M : Model σ X W) (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    At (evI F) (M.co.e.symm (fun i => liftA (a i), fun i => liftA (b i))) := by
  intro c hc
  rw [← map_smul]
  have : c • ((fun i => liftA (a i), fun i => liftA (b i)) : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = 0 := by
    ext i <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] <;>
      exact smul_liftA hc _
  rw [this, map_zero]

theorem arc_liftA {κ : Type} (a : κ → mixedEmbedding.mixedSpace F) : arc (fun i => liftA (a i)) = a := by
  funext i; exact evI_liftA (a i)

theorem actsD_iff_dOp {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have e : D u f = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
    ext x
    rw [(hD u hu f).2 x, dOp_apply]
    rfl
  have h1 : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
    (GlobalTheory.T.archActionReadings_compatible F _ f (D u f) (D u f)).1 _ (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
      (hD u hu f).1
  rw [← e]
  exact ⟨fun h2 => (GlobalTheory.T.archActionReadings_compatible F _ f f₁ (D u f)).2.2.1 _ h2 h1, fun h2 => h2 ▸ h1⟩

theorem isGauss_iff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (g : SInf F (Fin n × Fin d)) : M.IsGauss ψ τ g ↔ GaussD M τ g := by
  refine exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun H => ?_, fun H f f' hf hf' => ?_⟩
  · exact H _ _ ((actsD_iff_dOp hψ M u hu _ _).2 rfl) ((actsD_iff_dOp hψ M u' hu' _ _).2 rfl)
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 hf, (actsD_iff_dOp hψ M u' hu' _ _).1 hf']
    exact H

theorem pol_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    M.Pol ψ τ = sInf {N | (∀ f₀, GaussD M τ f₀ → f₀ ∈ N) ∧
      ∀ (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F), ∀ f ∈ N, dOp a b f ∈ N} := by
  unfold Model.Pol
  congr 1
  ext N
  simp only [Set.mem_setOf_eq]
  refine and_congr (forall_congr' fun f₀ => imp_congr_left (isGauss_iff hψ M τ f₀)) ⟨fun H a b f hf => ?_, fun H u hu f hf f₁ h1 => ?_⟩
  · have hu := at_symm M a b
    refine H _ hu f hf _ ((actsD_iff_dOp hψ M _ hu _ _).2 ?_)
    rw [LinearEquiv.apply_symm_apply, arc_liftA, arc_liftA]
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 h1]
    exact H _ _ f hf

theorem dOp_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ) :
    dOp a b f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ] at hf ⊢
  exact Submodule.mem_sInf.2 fun N hN => hN.2 a b f (Submodule.mem_sInf.1 hf N hN)

theorem gauss_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f : SInf F (Fin n × Fin d)} (hf : GaussD M τ f) : f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ]
  exact Submodule.mem_sInf.2 fun N hN => hN.1 f hf

end Gen

end GlobalTheory.ThK.EvAt0.PolEv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLattice
namespace GlobalTheory.OffIdem


open NumberField in
theorem exists_common {O R ι : Type} [CommRing O] [IsDomain O] [CommRing R] (f : O →+* R) (I : ι → Ideal O) (ε : R)
    (hε : ε * ε = ε) (P : Finset ι) (h : ∀ i ∈ P, ∃ x ∈ I i, x ≠ 0 ∧ ∃ s, ε = s * f x) :
    ∃ x, x ≠ 0 ∧ (∀ i ∈ P, x ∈ I i) ∧ ∃ s, ε = s * f x := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp, ε, by simp⟩
  | insert a P _ ih =>
    obtain ⟨x, hx0, hx, s, hs⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨y, hy, hy0, t, ht⟩ := h a (Finset.mem_insert_self _ _)
    refine ⟨x * y, mul_ne_zero hx0 hy0, fun i hi => ?_, s * t, ?_⟩
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Ideal.mul_mem_left _ _ hy
      · exact Ideal.mul_mem_right _ _ (hx i hi)
    · rw [map_mul, mul_mul_mul_comm, ← hs, ← ht, hε]

end GlobalTheory.OffIdem

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffIdem

theorem idemSum_mul_idemAt {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P)
    {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ P) : ∃ a : AE D, Formalism.L2.NTheta.IsIdemAt a PP ∧ a * e = a := by
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := h
  have h1 : ∀ i ∈ P, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P h1 hc
  refine ⟨es PP, hes PP hPP, ?_⟩
  rw [Finset.mul_sum, Finset.sum_eq_single PP (fun j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes PP hPP) (hes j hj) (hcross PP hPP j hj) (hcross j hj PP hPP) hji)
    (fun h => absurd hPP h), h1 PP hPP]

theorem exists_eq_mul_of_mul_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Finset (Formalism.L2.DIV.Pl E)) (ε : Formalism.L2.Herm.intAf F E) (hε : ε * ε = ε)
    (h : ∀ PP ∈ P, ∃ a : Formalism.L2.Herm.intAf F E, Formalism.L2.DIV.resS F PP a = 1 ∧ a * ε = 0) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ (∀ PP ∈ P, x ∈ PP.asIdeal) ∧ ∃ s, ε = s * Formalism.L2.DIV.oToS F E x :=
  exists_common (Formalism.L2.DIV.oToS F E) (fun PP : Formalism.L2.DIV.Pl E => PP.asIdeal) _ hε P fun PP hPP => by
    refine GlobalTheory.IdemRes.exists_eq_mul_of_resS_ne_one PP _ hε fun hne => ?_
    have := PP.isPrime
    obtain ⟨a, ha1, h0⟩ := h PP hPP
    have h3 := congrArg (Formalism.L2.DIV.resS F PP) h0
    rw [RingHom.map_mul, ha1, hne, RingHom.map_zero, one_mul] at h3
    exact one_ne_zero h3

theorem one_sub_mul_self {R : Type} [CommRing R] {e : R} (h : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  linear_combination h

theorem mul_one_sub {R : Type} [CommRing R] {a e : R} (h : a * e = a) : a * (1 - e) = 0 := by
  linear_combination -h

theorem mul_ringHom_mul_ringHom_inv_cancel {K R : Type} [Field K] [CommRing R] (f : K →+* R) (s : R) {y : K} (hy : y ≠ 0) :
    s * f y * f y⁻¹ = s := by
  rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hy, map_one, mul_one]

theorem exists_den {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) :
    ∃ y : 𝓞 D.host.E, (y : D.host.E) ≠ 0 ∧ (∀ PP ∈ P, y ∈ PP.asIdeal) ∧
      finPart D ((1 - e) * incA D ((y : D.host.E)⁻¹)) ∈ intAE D := by
  have h1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have h2 : (1 - e) * (1 - e) = 1 - e := one_sub_mul_self (R := AE D) h1
  have hint : toEAf D (1 - e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h2]))
  obtain ⟨y, hy0, hy, s, hs⟩ := exists_eq_mul_of_mul_eq_zero P ⟨toEAf D (1 - e), hint⟩
    (Subtype.ext (by change toEAf D (1 - e) * toEAf D (1 - e) = toEAf D (1 - e); rw [← RingHom.map_mul, h2]))
    fun PP hPP => by
      obtain ⟨a, ha, hae⟩ := idemSum_mul_idemAt he hPP
      obtain ⟨hai, ha1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D a PP ha
      refine ⟨_, ha1, Subtype.ext ?_⟩
      change toEAf D a * toEAf D (1 - e) = 0
      rw [← RingHom.map_mul, mul_one_sub (R := AE D) hae, RingHom.map_zero]
  have hs' : toEAf D (1 - e) = (s : Formalism.IndefR.Datum.EAf D) * eToEAf D (y : D.host.E) := congrArg Subtype.val hs
  have hy0' : (y : D.host.E) ≠ 0 := fun h => hy0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have h4 : toEAf D (incA D ((y : D.host.E)⁻¹)) = eToEAf D ((y : D.host.E)⁻¹) := rfl
  refine ⟨y, hy0', hy, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_⟩
  rw [RingHom.map_mul, h4, hs', mul_ringHom_mul_ringHom_inv_cancel (eToEAf D) _ hy0']
  exact s.2

theorem one_sub_smul_mem_latO : ∀ (D : D7) (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E)) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ x : WO V W, (∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∈ PP.asIdeal) → incA D (s : D.host.E) • x ∈ (latO V W LV LW fun _ => True)) → (1 - e) • x ∈ (latO V W LV LW fun _ => True) := by
  intro D V W LV LW e P he x hx
  obtain ⟨y, hy0, hy, hw⟩ := exists_den he
  have h5 := GlobalTheory.LatticeStable.smul_mem_latO D V W LV LW _ _ hw _ (hx y hy)
  rwa [smul_smul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hy0, RingHom.map_one, mul_one] at h5

end GlobalTheory.OffIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLatticeStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_idempotent_smul_mem_lattice : ∀ (D : D7) (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E)) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ x : WO V W, (∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∈ PP.asIdeal) → incA D (s : D.host.E) • x ∈ (latO V W LV LW fun _ => True)) → (1 - e) • x ∈ (latO V W LV LW fun _ => True) := by
  first | exact @GlobalTheory.OffIdem.one_sub_smul_mem_latO | exact GlobalTheory.OffIdem.one_sub_smul_mem_latO | (intros; apply GlobalTheory.OffIdem.one_sub_smul_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAlongSubset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeFlagUnipotentRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeFlagUnipotentRadical
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix

namespace GlobalTheory.StdPar

theorem unip_le_unipFlag_initCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S m hm hS g hg
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, h⟩ => h.trans (hS k hk), fun h => ⟨m, hm, h⟩⟩
  apply Subgroup.subset_closure
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · have key : ∀ y ∈ colSpan F X {l | ∃ k ∈ S, l ≤ k ∧ k < i.castLE m.2},
        ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j : Fin (m.val + 1), (S.filter fun k => k.val < i.val).card ≤
          (S.filter fun k => k.val < j.val).card → a j = 0) ∧ y = adMat F (initCols X m) *ᵥ a := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, ⟨k, hk, hlk, hki⟩, rfl⟩ := hy
        have hl : l.val < m.val + 1 := Nat.lt_succ_of_le (hlk.trans (hS k hk))
        refine ⟨Pi.single ⟨l.val, hl⟩ 1, fun j hj => ?_, ?_⟩
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          refine absurd hj (not_le.2 (Finset.card_lt_card ⟨fun t ht => ?_, fun h => ?_⟩))
          · rw [Finset.mem_filter] at ht ⊢
            exact ⟨ht.1, lt_trans (lt_of_lt_of_le ht.2 hlk) hki⟩
          · have := (Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨hk, hki⟩))).2
            exact absurd this (not_lt.2 hlk)
        · rw [mulVec_single_one]
          rfl
      | zero => exact ⟨0, fun _ _ => rfl, (mulVec_zero _).symm⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha, rfl⟩ := hy
        obtain ⟨b, hb, rfl⟩ := hz
        exact ⟨a + b, fun j hj => by rw [Pi.add_apply, ha j hj, hb j hj, add_zero], (mulVec_add _ _ _).symm⟩
      | smul c y _ hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        exact ⟨c • a, fun j hj => by rw [Pi.smul_apply, ha j hj, smul_zero], (mulVec_smul _ _ _).symm⟩
    have := (Subgroup.mem_iInf.1 hg.1 (i.castLE m.2)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
    obtain ⟨a, ha, e⟩ := key _ this
    refine ⟨a, ha, ?_⟩
    rw [sub_mulVec, one_mulVec]
    exact e
  · have := hg.2.2 (fun i => inclR (F := F) (AF F) (x i)) (by
      rw [e1, mem_colPerp_iff]
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    rw [e1, mem_colSpan_iff] at this
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

end GlobalTheory.StdPar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeFlagUnipotentRadicalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardParabolicUnipotent_le_flagUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := by
  first | exact @GlobalTheory.StdPar.unip_le_unipFlag_initCols | exact GlobalTheory.StdPar.unip_le_unipFlag_initCols | (intros; apply GlobalTheory.StdPar.unip_le_unipFlag_initCols <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeIsotropicFlagStabili
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeIsotropicFlagStabili
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
namespace GlobalTheory.StdParFlag

open Matrix

theorem unip_le_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)) (m : Fin r), T ⊆ S → m ∈ T → (∀ k ∈ T, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.parFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (T.filter fun k => k.val < i.val).card) := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S T m _ _ _
  classical
  have key : ∀ p ∈ GlobalTheory.StdPar.unip σ J X S, ∃ B : Matrix (Fin (m.val + 1)) (Fin (m.val + 1)) (AF F ⊗[F] E),
      B.BlockTriangular (fun i => (T.filter fun k => k.val < i.val).card) ∧
      (matHom _ σ J p).1 * adMat F (GlobalTheory.StdPar.initCols X m) = adMat F (GlobalTheory.StdPar.initCols X m) * B := by
    intro p hp
    have span_lemma : ∀ (i : Fin (m.val + 1)) (I : Set (Fin r)), (∀ l ∈ I, l.val < i.val) →
        ∀ y ∈ GlobalTheory.StdPar.colSpan F X I, ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j, i.val ≤ j.val → a j = 0) ∧
          adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a = y := by
      intro i I hI y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, hl, rfl⟩ := hx
        have hl' : l.val < m.val + 1 := by have := hI l hl; have := i.2; omega
        refine ⟨Pi.single ⟨l.val, hl'⟩ 1, fun j hj => Pi.single_eq_of_ne (fun e => ?_) _, ?_⟩
        · have := hI l hl; rw [e] at hj; simp at hj; omega
        · rw [mulVec_single_one]; rfl
      | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], by rw [mulVec_add]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨c • a, fun j hj => by simp [ha j hj], by rw [mulVec_smul]⟩
    have hcol : ∀ i : Fin (m.val + 1), ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j, (fun k : Fin (m.val + 1) => k.val) i ≤ (fun k : Fin (m.val + 1) => k.val) j → a j = 0) ∧
        ((matHom _ σ J p).1 - 1) *ᵥ (fun k => inclR (F := F) (AF F) (GlobalTheory.StdPar.initCols X m k i)) =
          adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a := by
      intro i
      have h := (Subgroup.mem_iInf.1 hp.1 (Fin.castLE m.2 i)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
      have hv : (fun k => inclR (F := F) (AF F) (GlobalTheory.StdPar.initCols X m k i)) = (adMat F X)ᵀ (Fin.castLE m.2 i) := rfl
      rw [hv, sub_mulVec, one_mulVec]
      obtain ⟨a, ha, e⟩ := span_lemma i _ (fun l hl => by
        obtain ⟨k, _, hlk, hki⟩ := hl
        have := Fin.lt_def.1 (lt_of_le_of_lt hlk hki)
        simpa using this) _ h
      exact ⟨a, ha, e.symm⟩
    obtain ⟨A, hA, e⟩ := lower_iff.1 hcol
    refine ⟨1 + A, fun l j hlt => ?_, ?_⟩
    · have hjl : j.val ≤ l.val := by
        by_contra hc
        refine absurd hlt (not_lt.2 (Finset.card_le_card fun k hk => ?_))
        simp only [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, by omega⟩
      have hne : l ≠ j := fun h => by subst h; exact lt_irrefl _ hlt
      rw [Matrix.add_apply, Matrix.one_apply_ne hne, hA l j hjl, add_zero]
    · rw [Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  intro p hp
  exact ⟨key p hp, key p⁻¹ (inv_mem hp)⟩

end GlobalTheory.StdParFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeIsotropicFlagStabiliStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardParabolicUnipotent_le_isotropicFlagStabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)) (m : Fin r), T ⊆ S → m ∈ T → (∀ k ∈ T, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.parFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (T.filter fun k => k.val < i.val).card) := by
  first | exact @GlobalTheory.StdParFlag.unip_le_parFlag | exact GlobalTheory.StdParFlag.unip_le_parFlag | (intros; apply GlobalTheory.StdParFlag.unip_le_parFlag <;> assumption)
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.ConstTrans
open GlobalTheory.StdPar GlobalTheory.Cusp

theorem unip_eq_unipFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S = GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := fun F E _ _ _ _ _ σ h n J hJ r X Y hW S m hm hm' => le_antisymm (GlobalTheory.T.standardParabolicUnipotent_le_flagUnipotentRadical F E σ h n J hJ r X Y hW S m hm hm') (GlobalTheory.T.flagUnipotentRadical_le_standardParabolicUnipotent F E σ h n J hJ r X Y hW S m hm hm')
theorem unip_le_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)) (m : Fin r), T ⊆ S → m ∈ T → (∀ k ∈ T, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.parFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (T.filter fun k => k.val < i.val).card) := GlobalTheory.T.standardParabolicUnipotent_le_isotropicFlagStabiliser

end GlobalTheory.ConstTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.DefRank

theorem rank_le_bigN : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node),
    DefNode D.R.m X → (G.V X).rank ≤ bigN D := by
  intro D T L sc G X hX
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hm := D.R.two_le_m
  rcases X with ⟨_ | i, j⟩ | i | j
  · obtain rfl := hX.2
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e, D.sp.X'_rank]
    show D.R.r + D.R.m * D.R.t ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · obtain ⟨hi, rfl⟩ := hX
    rw [(G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (by simp)).rank]
    show D.R.r + D.R.m * D.R.t + (i + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have := Nat.mul_le_mul_right (sLen D) hi
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · exact hX.elim
  · rw [(G.isV (X := .top j) hX (by simp)).rank]
    show nRk D + D.R.m * (sLen D - 1) + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have h1 := Nat.mul_le_mul_right (D.R.t + 1) (show j ≤ D.R.m from hX)
    have hs : sLen D - 1 + 1 = sLen D := by unfold sLen; omega
    have hn : nRk D = D.R.r + 1 := rfl
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * (sLen D - 1) + D.R.m * (D.R.t + 1) + D.R.m := by
      conv_lhs => rw [← hs]
      ring
    have h2 : j * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := h1
    omega

end GlobalTheory.DefRank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteKernelNode_rank_le_totalRank : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node), DefNode D.R.m X → (G.V X).rank ≤ bigN D := by
  first | exact @GlobalTheory.DefRank.rank_le_bigN | exact GlobalTheory.DefRank.rank_le_bigN | (intros; apply GlobalTheory.DefRank.rank_le_bigN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.SumCount

section

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def DataNum : Prop := (Nat.card ch.G.Datum : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def CosNum : Prop := ∀ Φ, ((ch.S.supp A.μ0 Φ).ncard : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def PureNum : Prop := ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ τ,
  IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) τ →
    (τ.support.card : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

end

def DataK : Prop := BigC fun _ ch C b => DataNum ch C b

def CosK : Prop := BigC fun _ ch C b => CosNum ch C b

def PureK : Prop := BigC fun _ ch C b => PureNum ch C b


open IsDedekindDomain NumberField Matrix in
theorem _root_.GlobalTheory.SumCount.infCountK_of (h1 : _root_.GlobalTheory.SumCount.DataK)
    (h2 : _root_.GlobalTheory.SumCount.CosK) (h3 : _root_.GlobalTheory.SumCount.PureK) :
    _root_.GlobalTheory.SumSize.InfCountK := by
  unfold _root_.GlobalTheory.SumSize.InfCountK
  obtain ⟨s₁, h1⟩ := h1
  obtain ⟨s₂, h2⟩ := h2
  obtain ⟨s₃, h3⟩ := h3
  refine ⟨max s₁ (max s₂ s₃), fun CF hCF ↦ ?_⟩
  obtain ⟨C1, h1⟩ := h1 CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, h2⟩ := h2 CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C3, h3⟩ := h3 CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C1 (max C2 C3), fun ε C hC ↦ ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x2, h2⟩ := h2 ε C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC)
  obtain ⟨x3, h3⟩ := h3 ε C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC)
  refine ⟨max x1 (max x2 x3), fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hR ch hch hs hf ↦ ?_⟩
  have a1 := h1 D large₂ he (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hR ch hch hs hf
  have a2 := h2 D large₂ he (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx)
    Γ Pl0 T A Ks R F hR ch hch hs hf
  have a3 := h3 D large₂ he (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)
    Γ Pl0 T A Ks R F hR ch hch hs hf
  exact ⟨a1, fun Φ ↦ ⟨a2 Φ, a3 Φ⟩⟩

end GlobalTheory.SumCount

end
end
