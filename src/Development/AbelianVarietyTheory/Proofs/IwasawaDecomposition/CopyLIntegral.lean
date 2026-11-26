module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.DatCopy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def setIo (R : RealDat3 D A Ks) (y : type_of% R.ioY) (x : type_of% R.ioX) : RealDat3 D A Ks :=
  { R with ioY := y, ioX := x }

end Gen

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Three

set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) {F : Face3 a.D A}

def twice : RealDat3 a.D A Ks := (by with_unfolding_all exact ((real3 (a := b) a (iK := alg b iK) (real3 b R)) :))

def twiceY : type_of% R.ioY := by
  with_unfolding_all exact ((twice b R).ioY :)

def twiceX : type_of% R.ioX := by
  with_unfolding_all exact ((twice b R).ioX :)

theorem twiceY_eq : R.ioY = twiceY b R := by
  apply eq_of_heq
  with_unfolding_all
    exact (HEq.trans (real_ioY b R.toRealDat)
      (real_ioY (a := b) a (iK := alg b iK) (real b R.toRealDat)) :)

theorem twiceX_eq : R.ioX = twiceX b R := by
  apply eq_of_heq
  with_unfolding_all
    exact (HEq.trans (real_ioX b R.toRealDat)
      (real_ioX (a := b) a (iK := alg b iK) (real b R.toRealDat)) :)

theorem twice_eq : R = twice b R := (by with_unfolding_all exact ((congrArg₂ (setIo R) (twiceY_eq b R) (twiceX_eq b R)) :))

variable {R}

theorem holds_back (h : letI := alg b iK; Holds (real3 b R) (face3 b F)) : Holds R F := by
  have h2 := holds_tr (a := b) a (iK := alg b iK) h
  exact (by with_unfolding_all exact ((cast (congrArg (fun R' : RealDat3 a.D A Ks => Holds R' F) (twice_eq b R).symm) ((h2))) : _))

theorem rowTest_tr (h : Rat.RowTest (R.toCx3 F)) : letI := alg b iK; Rat.RowTest ((real3 b R).toCx3 (face3 b F)) := by
  with_unfolding_all
    exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => Rat.RowTest X) (toCx3_eq b R F)).mp h :)

end Three

theorem multEq_tr {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} (h : GlobalTheory.CuspMult.MultEq R) :
    letI := alg b iK; GlobalTheory.CuspMult.MultEq (real b R) := by
  intro i M₀ j Φ hI W _ _ σ h1 h2 h3
  have key := h ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact ((ds a M₀) :))) ((by with_unfolding_all exact (j :))) ((by with_unfolding_all exact (Φ :))) ⟨(by with_unfolding_all exact (hI.isom :)), (by with_unfolding_all exact (hI.conj :)), (by with_unfolding_all exact (hI.frame :))⟩ W ((by with_unfolding_all exact (σ :))) ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact (h3 :)))
  delta GlobalTheory.CuspMult.cuspMult GlobalTheory.CuspMult.allMaps
  rewrite [mult_eq a b]
  exact (by with_unfolding_all exact (key :))

section Dat

variable {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {Tw : Top.TwDat B} {Wt : Set B.places.Pl}


set_option maxHeartbeats 2000000 in
def copy (s : SameGrp a b) (z : Dat a.st I hX Tw Wt) : Dat b.st I hX Tw Wt :=
  @Dat.mk b.st px I hX Tw Wt z.Xg z.tr (coreJ b z.core) ((by with_unfolding_all exact ((alg b z.alg) :))) ((by with_unfolding_all exact (z.alg_eq :))) ((by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :)))
    ((by with_unfolding_all exact ((z.cG.trans s.iso) :))) ((by with_unfolding_all exact ((geoHalf b (iK := z.alg) z.geo) :))) ((by with_unfolding_all exact ((pins_tr b (iK := z.alg) s z.pins) :)))
    ⟨(by with_unfolding_all exact ((levIs_tr b z.lev.is) :)), (by with_unfolding_all exact ((congrArg (chFr b) z.lev.C) :)), (by with_unfolding_all exact (z.lev.xiH :)), (by with_unfolding_all exact (z.lev.Pg :)), (by with_unfolding_all exact (z.lev.Q :)), (by with_unfolding_all exact (z.lev.beta :))⟩
    ((by with_unfolding_all exact (z.idG :)))
    (by
      have h := (goodSet_iff a.st (px := px) _ _).1 z.good
      have e : ∀ g, a.D.ntypes.e0.coeff ((z.R.eG.trans z.cG) g) = b.D.ntypes.e0.coeff (((z.R.eG.trans z.cG).trans s.iso) g) :=
        fun g => (s.e0 _).symm
      simp only [e] at h
      exact (by with_unfolding_all exact (((goodSet_iff b.st (px := px) ((z.R.eG.trans z.cG).trans s.iso) z.Xg).2 h) :)))
    ((by with_unfolding_all exact (z.mu :))) ((by with_unfolding_all exact (z.fieldValues_mem_fixedField :))) ((by with_unfolding_all exact (z.Ks_le :)))

variable (s : SameGrp a b) {z : Dat a.st I hX Tw Wt}

theorem copy_exAt (h : z.R.toRealDat.ExAt) : (copy b s z).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr b (iK := z.alg) h) :))

theorem copy_lUnif (h : z.R.toRealDat.LUnif) : (copy b s z).R.toRealDat.LUnif := (by with_unfolding_all exact (h :))

theorem copy_lIntegral (h : z.R.toRealDat.LIntegral) : (copy b s z).R.toRealDat.LIntegral := (by with_unfolding_all exact (h :))

theorem copy_multEq (h : GlobalTheory.CuspMult.MultEq z.R.toRealDat) : GlobalTheory.CuspMult.MultEq (copy b s z).R.toRealDat :=
  (by with_unfolding_all exact ((multEq_tr b (iK := z.alg) h) :))

theorem copy_rowTest (h : Rat.RowTest (z.R.toCx3 z.F)) : Rat.RowTest ((copy b s z).R.toCx3 (copy b s z).F) :=
  (by with_unfolding_all exact ((rowTest_tr b (iK := z.alg) h) :))

theorem holds_of_copy (h : Holds (copy b s z).R (copy b s z).F) : Holds z.R z.F := holds_back b (iK := z.alg) ((by with_unfolding_all exact (h :)))

end Dat

end GlobalTheory.Mem.R3.DatCopy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

namespace GlobalTheory.Mem.R3.LedRec


set_option maxHeartbeats 1000000 in
theorem ev_exists_sizeData : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w j, X.toD7.what₂.Aj j w = 0) →
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧
      8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) (fun w _ j _ _ => hA w j)
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  exact ⟨L, e1, M.sizes, ⟨M.params⟩, M.parT.nV_ge⟩

def bare {B : Base} {C : Cols B} (W : RowsRest B C) : RowsRest B C :=
  { GaloisStage.adapt W with Ij := fun _ _ _ => 0, jw := fun _ _ _ => 0 }

theorem exists_bare (hG : GlobalTheory.Published.GreenCuspidal) {B : Base} {C : Cols B} (a : Late B C) (f : Fr B.toPre) (η : ℝ) :
    ∃ b : Late B C, GrpTrue b.N f ∧ b.V.div.etaF = η ∧ ∀ w j, b.D.what₂.Aj j w = 0 := by
  obtain ⟨N, -, -, hN, -⟩ := exists_nStage_grpTrue hG B C (bare a.W) (GlobalTheory.MemN.shaOK_shaTrue B.toPre) (fun _ _ _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) f
  exact ⟨⟨bare a.W, { a.V with div := { a.V.div with etaF := η } }, { a.S with }, N, a.G⟩, hN, rfl, fun _ _ => rfl⟩

def sameGrp {B : Base} {C : Cols B} {a b : Late B C} {f : Fr B.toPre} (h : GrpTrue a.N f) (h' : GrpTrue b.N f) : SameGrp a b where
  e := plEquiv a.N.naut b.N.naut
  pl := TypesTrue.plGw_plEquiv h h'
  e0 := h.typeIdempotent_coeff_across_layers h'

end GlobalTheory.Mem.R3.LedRec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitEmb
open GlobalTheory.SplitLift

section General
variable {n : ℕ} {K : Type*} (A : Type*) [CommRing K] [CommRing A]

def triMat (M : GL (Fin n) K) : Matrix (Fin n) (Fin n) (K × K × A) :=
  fun i j => ((M : Matrix (Fin n) (Fin n) K) i j, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j i,
    (1 : Matrix (Fin n) (Fin n) A) i j)

theorem triMat_one : triMat A (1 : GL (Fin n) K) = 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [triMat, inv_one, Units.val_one, Matrix.one_apply, eq_comm (a := j)]
  split_ifs <;> rfl

theorem triMat_mul (M N : GL (Fin n) K) : triMat A (M * N) = triMat A M * triMat A N := by
  symm
  apply matrix_prod_ext
  · exact Matrix.map_mul (L := triMat A M) (M := triMat A N) (f := RingHom.fst K (K × A))
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.fst K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    change ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose *
      ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose =
      (((M * N)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.snd K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    exact Matrix.mul_one (1 : Matrix (Fin n) (Fin n) A)

end General

theorem exists_hom_trivOutside_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L),
    ∃ e : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) →* GAf L n,
      (∀ g, TrivOutside {s.v} (e g)) ∧ ∀ g, s.loc n (e g) = g := by
  intro L _ _ _ n s
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : IsCMField.complexConj L (δ * δ) = δ * δ := by rw [map_mul, hδ]; ring
  let d : maximalRealSubfield L := ⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩
  have hd : δ * δ = algebraMap (maximalRealSubfield L) L d := rfl
  have hr : s.i δ ≠ 0 := (map_ne_zero _).2 hδ0
  let X : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) → Matrix (Fin n) (Fin n) (AL L) :=
    fun M => (triMat (AL L) M).map (θ s δ d hd hr)
  have hX1 : X 1 = 1 := by
    show (triMat (AL L) 1).map (θ s δ d hd hr) = 1
    rw [triMat_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXm : ∀ M N, X (M * N) = X M * X N := fun M N => by
    show (triMat (AL L) (M * N)).map (θ s δ d hd hr) = _
    rw [triMat_mul, Matrix.map_mul]
  have hconj : ∀ M, conjT (conjAL L) (X M) = X M⁻¹ := fun M => by
    refine Matrix.ext fun i j => ?_
    simp only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]
    rw [conj_θ s δ d hd hr hδ]
    congr 1
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [triMat, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have hX : ∀ M, X M * conjT (conjAL L) (X M) = 1 := fun M => by
    rw [hconj, ← hXm, mul_inv_cancel, hX1]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := fun M => ⟨⟨X M, conjT (conjAL L) (X M), hX M, mul_eq_one_comm.mp (hX M)⟩, hX M⟩
      map_one' := Subtype.ext (Units.ext hX1)
      map_mul' := fun M N => Subtype.ext (Units.ext (hXm M N)) }
  refine ⟨e, fun M w hw => ?_, fun M => ?_⟩
  · have hw' : w ≠ s.v := hw
    refine Matrix.ext fun i j => ?_
    change compAt L w (θ s δ d hd hr (triMat (AL L) M i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [compAt_θ s δ d hd hr _ hw']
    simp only [triMat, Matrix.one_apply]
    split_ifs <;> simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change s.proj (θ s δ d hd hr (triMat (AL L) M i j)) = _
    rw [proj_θ]
    rfl

end GlobalTheory.SplitEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LabelMapLabelOfClassFunctionLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LabelMapLabelOfClassFunctionLabel
open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

theorem getElem_of_canonList_eq {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (Q : List (GlobalTheory.GLq.Pc g))
    (h : canonList b lam = Q) (c : Fin s) (hc : (c : ℕ) < Q.length) :
    Q[(c : ℕ)] = ⟨Fintype.card {i // b i = c},
      fun x => (Formalism.IrreducibleCountingLemmas.TYPES.transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ := by
  subst h
  have e : (List.finRange s)[(c : ℕ)]'(by simp) = c := by simp
  simp only [canonList, List.getElem_map]
  rw [e]

theorem hasLabelO_of_hasLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) → P = O.lab d V) → (∀ (d : ℕ) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCusp χ → ∃ V : FDRep ℂ (GL (Fin d) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = χ x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → (∀ (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f := by
  intro g _ L C O hU hReal hTr hCon hSurj r τ f hτ hL
  obtain ⟨Q, hQ, hdeg, hf, hip⟩ := hL
  subst hdeg
  have hQScusp : ∀ p ∈ (Q.map Prod.snd), 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hc : GlobalTheory.GLq.IsCusp q.2.2 := (hQ q hq).2.1
    exact ⟨hc.1, hReal _ _ hc⟩
  obtain ⟨b, lam, hb, hlam, hcan⟩ := hSurj (Q.map Prod.snd) hQScusp
  have key : ∀ c : Fin (Q.map Prod.snd).length, ∀ hcQ : (c : ℕ) < Q.length,
      Formalism.IrreducibleCountingLemmas.TYPES.labO O (lam c) = (Q[(c : ℕ)]'hcQ).1 := by
    intro c hcQ
    have hcusp := hQ _ (List.getElem_mem hcQ)
    have h2 : (Q[(c : ℕ)]'hcQ).2 = (Q.map Prod.snd)[(c : ℕ)] := by simp
    rw [h2, getElem_of_canonList_eq b lam (Q.map Prod.snd) hcan c c.2] at hcusp
    exact (hU _ _ _ hcusp.2.1.1 (Formalism.L2.PT.simple_transp _ (hlam c).1)
      (Formalism.L2.PT.isCuspidal_transp _ (hlam c).2) hcusp).symm
  refine ⟨(Q.map Prod.snd).length, b, lam, hb, hlam, ?_, ?_⟩
  · rw [hCon _ _ b lam τ hτ]
    have htr : (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam)
        (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) = GlobalTheory.GLq.hcL (Q.map Prod.snd) (GlobalTheory.GLq.degL (Q.map Prod.snd)) := by
      funext x
      rw [hTr _ _ b lam hb x, hcan]
    rw [htr]
    exact hip
  · have hlen : (Q.map Prod.fst).length = (Q.map Prod.snd).length := by simp
    rw [hf, ← Fin.prod_univ_getElem (Q.map Prod.fst)]
    refine Fintype.prod_equiv (finCongr hlen) _ _ (fun c => ?_)
    have hcQ : (c : ℕ) < Q.length := by simpa using c.2
    rw [key _ hcQ]
    simp

end GlobalTheory.SerCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LabelMapLabelOfClassFunctionLabelStatement
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelMap_label_of_classFunctionLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) → P = O.lab d V) → (∀ (d : ℕ) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCusp χ → ∃ V : FDRep ℂ (GL (Fin d) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = χ x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → (∀ (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f := by
  first | exact @GlobalTheory.SerCmp.hasLabelO_of_hasLabel | exact GlobalTheory.SerCmp.hasLabelO_of_hasLabel | (intros; apply GlobalTheory.SerCmp.hasLabelO_of_hasLabel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotent
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem GlobalTheory.SerCmp.eSerC_eq_eSerO : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : IsGenSys L.gen), t = L.teich → ∀ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht L.gen hζ), (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht L.gen hζ) τ (O.lab d τ)) → ∀ (r : ℕ) (f : (ZMod g)[X]), 1 ≤ r → GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  intro hG g _ L t ht hζ htL O hO r f hr
  have hcusp : ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x) :=
    fun d V hd hs hc => GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel g L t ht hζ htL d V _ hd ((GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc)
      (hO d V hd hs hc)
  have hB : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), CategoryTheory.Simple τ →
      (GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f ↔ Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f) := by
    intro τ hτ
    constructor
    · refine GlobalTheory.T.labelMap_label_of_classFunctionLabel g L O (fun d V P hd hs hc hP => ?_) (fun d χ hχ => ?_)
        (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g) (GlobalTheory.T.exists_blocks_of_cuspidal_character_list g) r τ f hτ
      · exact GlobalTheory.T.cuspidal_label_polynomial_unique_all_primes hG g L d P (O.lab d V) _ hP (hcusp d V hd hs hc)
      · obtain ⟨V, hV, hVχ⟩ := hχ.2.1
        have hχV : (fun x => V.character x) = χ := funext hVχ
        have hd : 1 ≤ d := hχ.1
        exact ⟨V, hV, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hV).1 (hχV ▸ hχ), hVχ⟩
    · exact GlobalTheory.T.classFunctionLabel_of_labelMap_label g L O hcusp (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g) r τ f hτ
  unfold GlobalTheory.GLq.eSerC Formalism.L2.NT.eSerO
  rw [GlobalTheory.T.finsum_centralIdempotentOfIrrCharacter_eq_simple]
  refine finsum_congr fun z => finsum_congr_Prop (propext ?_) fun _ => rfl
  constructor
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).1 hl⟩
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).2 hl⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : IsGenSys L.gen), t = L.teich → ∀ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht L.gen hζ), (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht L.gen hζ) τ (O.lab d τ)) → ∀ (r : ℕ) (f : (ZMod g)[X]), 1 ≤ r → GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  first | exact @GlobalTheory.SerCmp.eSerC_eq_eSerO | exact GlobalTheory.SerCmp.eSerC_eq_eSerO | (intros; apply GlobalTheory.SerCmp.eSerC_eq_eSerO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TupTieW

theorem tupTied_of_muIsW : ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl) (xi : X.C.Tup → HChar X.B.host.E), V4.MuIsW X f T Wt xi → (∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt) ∧ Wt.Finite ∧ (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) ∧ ∀ nch : NChoice X.toD7, (∀ w ∈ Wt, nch.Q w = T.Q w) → ∃ tp : TupTied X.toD7 (Fr.at X f) nch, tp.xi = xi ∧ tp.psi = T.psi := by
  intro X f T Wt xi h
  have key : ∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt := by
    intro w
    constructor
    · intro hw
      by_contra hn
      exact hw (h.off w hn)
    · intro hw he
      have he' : X.W.muAt w = X.C.mu0 := he
      rw [h.on w hw] at he'
      have h1 := h.tw w
      rw [he', h.mu0] at h1
      exact (TwFin.tw_fin X.B f T).2.1 w h1.symm
  have hfin : Wt.Finite :=
    Set.Finite.subset (TwFin.tw_fin X.B f T).2.2.2 fun w hw => h.sub w hw
  have hconj : ∀ w ∈ Wt, X.B.places.conj w ∈ Wt := by
    intro w hw
    refine (key _).1 ?_
    have hc : X.toD7.what₂.muAt (X.toD7.what₂.places.conj w) = X.toD7.what₂.muAt w :=
      X.toD7.what₂.muAt_conj w
    intro he
    exact (key w).2 hw (hc.symm.trans he)
  refine ⟨key, hfin, hconj, fun nch hQ => ?_⟩
  have hg : ∀ μ, TupTie.Good X.B.host.F (xi μ) :=
    fun μ => TupTie.good_set f T (h.range ▸ Set.mem_range_self μ)
  refine ⟨⟨xi, h.inj, fun μ => (hg μ).1, fun μ => (hg μ).2.1, fun μ => (hg μ).2.2, T.psi, h.mu0, h.star, h.star', h.tw,
    fun w hw => ?_, fun w hw => ?_⟩, rfl, rfl⟩
  · rw [hQ w ((key w).1 hw)]
    exact T.psi_is w
  · exact h.supp w fun hn => (key w).2 hn hw

end GlobalTheory.Mem.Top.TupTieW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlot
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem SecondG.sAnd_of_largeBase : ∀ (KP : GroupRetwisting.BaseP) (Q Q' R : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.LargeBaseConditionG KP Q R → GroupRetwisting.SecondG KP Q Q' →
    GroupRetwisting.SecondG KP Q (sAnd Q' R) := by
  intro KP Q Q' R hK hR hS
  refine (EvG.inter hR hS).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨S₁r, P₁r, Ar, S₂r, r1, r2, hr⟩, ⟨S₁s, P₁s, As, S₂s, s1, s2, hs⟩⟩ := H
  refine ⟨fun P g F => S₁s P g F ∪ S₁r P g F, fun P g F F₀ => P₁s P g F F₀ ∪ P₁r P g F F₀, As, S₂s, ?_, s2, ?_⟩
  · intro P g F z hz
    rcases Finset.mem_union.1 hz with h | h
    exacts [s1 _ _ _ z h, r1 _ _ _ z h]
  · intro B f T hO hH hP hA hKP hT C W V S N G c hQ hX A S₂ hS₂
    have hH' : Has₂ B (S₁s B.toPre f B.KsC) (S₂s B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨B', f', T', hEnl, hf', hpl, hAv, hS', C', W', V', S', N', G', c', hQ', hTw, hQ''⟩ :=
      hs B f T hO hH' (fun x hx => hP (Finset.mem_union_left _ hx)) hA hKP hT C W V S N G c hQ hX
        (fun l => A l ∪ Ar B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂r P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
        (by
          intro P g Ξ z hz
          rcases Finset.mem_union.1 hz with h | h
          exacts [hS₂ _ _ _ z h, r2 _ _ _ _ _ z h])
    have hP' : B'.toPre = B.toPre := hEnl.1
    have cf : ∀ {α : Type} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {x : Fr P} {y : Fr P'}, P = P' → HEq x y → g P x = g P' y := by
      intro α g P P' x y h hxy
      subst h
      rw [eq_of_heq hxy]
    have hk : B'.KsC = B.KsC := hEnl.KsC_eq
    have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := hEnl.fixedCoefficientField_eq
    have hRc : R K ⟨B', C', W', V', S', N', G'⟩ f' T' c' :=
      hr B' f' T' (hP' ▸ hO)
        ⟨by rw [hk, hl, cf S₁r hP' hf']; exact fun z hz => hH.1 z (Finset.mem_union_right _ hz),
          by rw [hk, hl]; exact fun z hz => hS' z (Finset.mem_union_right _ hz)⟩
        (by rw [hk, hl, cf P₁r hP' hf', hpl]; exact fun x hx => hP (Finset.mem_union_right _ hx))
        (by
          rw [hk, hl, cf Ar hP' hf']
          exact fun w v hv h => hAv w v hv (Finset.mem_union_right _ h))
        (hK.enl B B' f f' hEnl hf' hKP) C' W' V' S' N' G' c' hQ'
    exact ⟨B', f', T', hEnl, hf', hpl, fun w v hv h => hAv w v hv (Finset.mem_union_left _ h),
      fun z hz => hS' z (Finset.mem_union_left _ hz), C', W', V', S', N', G', c', hQ', hTw, hQ'', hRc⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlotStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondG_sAnd_of_largeBase : ∀ (KP : GroupRetwisting.BaseP) (Q Q' R : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.LargeBaseConditionG KP Q R → GroupRetwisting.SecondG KP Q Q' → GroupRetwisting.SecondG KP Q (sAnd Q' R) := by
  first | exact @GlobalTheory.Mem.Top.GroupRetwisting.SecondG.sAnd_of_largeBase | exact GlobalTheory.Mem.Top.GroupRetwisting.SecondG.sAnd_of_largeBase | (intros; apply GlobalTheory.Mem.Top.GroupRetwisting.SecondG.sAnd_of_largeBase <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem descend_exists (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∃ Φ : S.WL j →+ FmT D T S i j b, (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) ∧
      (∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x)) ∧
      ∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w := by
  obtain ⟨n, bs, hb, -, hKs, hLi, hLs⟩ := In.ks j h1 h2
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  exact GlobalTheory.T.exists_semilinear_descent_to_baseChange_of_form D.LL0 S.kKs S.kKs_spec (WKr D S j) bs (fun k => hW ▸ hb k) (hW ▸ hKs) hLi hLs
    (KT := KT D T i b) (readK D T i b) (fun s => rfl)

theorem descend_actL (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hf : ∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x))
    (g : G0g D.nd) (x : S.WL j) :
    Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x) := by
  have hcR : cR D S In.chi j (S.eG.symm g) = chiL S j (In.chi j h1 h2) (S.eG.symm g) := by
    unfold cR; rw [dite_eq_left ⟨h1, h2⟩]
  change _ = ((readK D T i b (cR D S In.chi j (S.eG.symm g)))⁻¹ •
    Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (rhoR D S In.rho j (S.eG.symm g))) (Φ x)
  rw [hcR]
  have e1 : actL D S j g x = (((chiL S j (In.chi j h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) •
      (S.A j).ρ (S.eG.symm g) x := by
    simp only [actL, chiL, IntermediateField.coe_inv, LinearMap.smul_apply]
  rw [e1, hc, hf ((S.A j).ρ (S.eG.symm g)) (rhoR D S In.rho j (S.eG.symm g)) (fun w => rfl), map_inv₀]
  rfl

theorem descend_eSum (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (x : S.WL j) :
    Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x) := by
  haveI : Fintype (G0g D.nd) := Fintype.ofFinite _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum]
  unfold eGT
  rw [MonoidAlgebra.lift_apply]
  simp only [eAlgT, MonoidAlgebra.coeff_ofCoeff]
  rw [Finsupp.sum_fintype _ _ (by intro; simp), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, hc, ha]
  simp

theorem descend_mem_V0T (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (he : ∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x))
    (x : S.WL j) (hx : x ∈ goodL D S In.θ j) : Φ x ∈ V0T D T S In.rho In.chi In.θ i j b := by
  rw [goodL, Submodule.mem_inf, Submodule.mem_iInf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨Φ x, ?_, ?_⟩
  · rw [SetLike.mem_coe, Fm0T, Submodule.mem_iInf]
    intro u
    rw [LinearMap.mem_ker, LinearMap.sub_apply]
    have h := hx2 u
    rw [Module.End.mem_eigenspace_iff] at h
    rw [LinearEquiv.coe_coe, ← ha, h, hc]
    simp [psiUT]
  · rw [Module.End.mem_eigenspace_iff, one_smul] at hx1
    rw [← he, hx1]

theorem descend_mem_eigenspace (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hf : ∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x))
    (k : ℕ) (P : PlE D.host) (μ : ↥D.LL0) (x : S.WL j)
    (hx : x ∈ Module.End.eigenspace (In.hL j k P) (μ : D.what₂.LL)) :
    Φ x ∈ Module.End.eigenspace (hkT D T S In i j b k P)
      (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b μ) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hw : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    split_ifs with h
    · rfl
    · exact absurd ⟨h1, h2⟩ h
  change ((show KT D T i b from algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k •
    LinearMap.baseChange (KT D T i b) (hLr D S In j k P) (Φ x) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = _
  rw [← hf _ _ hw, hx, hc]
  exact smul_smul _ _ _

end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem hA_symVec_sub_ite_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → ∀ (a : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posE D a then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  intro D X w k hg a j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.epsW X w i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 a).2.1
    · exact ((X.weightVectorsIntegral _).2.2 a).2.2.2
  refine wInt_of_zmod X k hg ?_
  have ha := a.2
  have hpos : (GlobalTheory.Mem.SymChar.Resid.posE D a).1 = a.1 := rfl
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1]
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.gramIntegral ⟨j.1, h1⟩ a).2.2
    rw [map_sub, ← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm] at h
    by_cases e : j = GlobalTheory.Mem.SymChar.Resid.posE D a
    · rw [if_pos e]
      rwa [if_pos (Fin.ext (by have := congrArg Fin.val e; simp only at this ⊢; omega)), map_one] at h
    · rw [if_neg e]
      rwa [if_neg (fun h' => e (Fin.ext (by have := congrArg Fin.val h'; simp only at this; omega))),
        map_zero] at h
  rw [dite_eq_right h1]
  have hne : ¬ j = GlobalTheory.Mem.SymChar.Resid.posE D a := fun e => by
    have := congrArg Fin.val e; rw [hpos] at this; omega
  rw [if_neg hne, sub_zero]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]; exact hW _
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4]; exact (X.formsAtZero.2 a).2
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3]; exact (X.gramIntegral a _).2.1
  · rw [dite_eq_right h3, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagDualVector_pairing_symmetricFrame_mod_place : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → ∀ (a : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.f0 a) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posE D a then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  first | exact @GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt | exact GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar.Resid

theorem hA_bwd_symVec : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.SymFrame.EwAt X w → 1 - X.ew ∈ GlobalTheory.Mem.SymChar.wInt X w → ∀ (i : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bwd i) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posB D i then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  intro D X w k hg hw hew i j
  have hZ : ∀ {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}, ZMod' X.B.I X.B.g c → c ∈ wInt X w :=
    fun hc => wInt_of_zmod X k hg hc
  have he : GlobalTheory.Mem.SymFrame.epsW X w = X.bw := by
    unfold GlobalTheory.Mem.SymFrame.epsW; rw [if_pos hw]
  have hr := rank_eq D
  have hp : (j = posB D i) ↔ j.1 = D.R.rS + i.1 := by rw [Fin.ext_iff]; rfl
  have hi := i.2
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  rw [he]
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 _).2.2.1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]
    have hd := X.bw_dual i ⟨j.1 - D.R.rS, by omega⟩
    by_cases hl : j.1 = D.R.rS + i.1
    · rw [if_pos (hp.2 hl)]
      rw [if_pos (Fin.ext (by simp only; omega))] at hd
      have := sub_mem (hZ hd) hew
      convert this using 1
      ring
    · rw [if_neg (fun h => hl (hp.1 h))]
      rw [if_neg (fun h => hl (by have := congrArg Fin.val h; simp only at this; omega))] at hd
      simpa using hZ hd
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g (X.weightVectorsIntegral i).2.1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3, if_neg (by rw [hp]; omega), sub_zero]
    apply hZ
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 _).2.2.2
  · rw [dite_eq_right h3, if_neg (by rw [hp]; omega), sub_zero, hA_zero_right']
    exact zero_mem _

end GlobalTheory.Mem.SymChar.Resid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentDualVector_pairing_symmetricFrame_mod_place : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.SymFrame.EwAt X w → 1 - X.ew ∈ GlobalTheory.Mem.SymChar.wInt X w → ∀ (i : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bwd i) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posB D i then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  first | exact @GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec | exact GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec | (intros; apply GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExactOfIsAdelicPointOfFramedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExactOfIsAdelicPointOfFramedLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem frExact_of_isPtOf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ), (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → ∀ {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}, IsPtOf hc g p → g ∈ UAd hc n ∧ FrExact q g p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q K _ Θ q hQ g p hp
  have h1 : IsPtOf hc (g * 1) p := by rwa [mul_one]
  have hres : ∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 (((1 : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 r j))
      (if j = r then (((1 : DiaG (E := E) (ST := ST)) P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) else 0) := by
    intro P r j _
    rw [inv_one, Units.val_one]
    by_cases h : j = r
    · subst h
      rw [Matrix.one_apply_eq, map_one, if_pos rfl]
      simpa using hasRes_coe P.1 1
    · rw [Matrix.one_apply_ne (Ne.symm h), map_zero, if_neg h]
      simpa using hasRes_coe P.1 0
  obtain ⟨hU, hd⟩ := GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul F E hc n ST SG Q g 1 p 1 h1 ⟨DecoF.base E n ∅ ∅ ∅, isPtOf_base hc, rfl⟩
    (fun w _ => map_one _) hres
  rw [DecoSet.dia_one] at hd
  refine ⟨hU, hd, fun P => Units.ext (Matrix.ext fun i j => ?_)⟩
  rw [qdf_at_val]
  show qPi q P ((g : Matrix (Fin n) (Fin n) _) i j) = q.phi P (((qGL n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [qsp_toGLm_apply]
  exact GlobalTheory.T.splitLocalLevel_firstFactor_reads_component hc n q P (hQ P) _ _ (hp.fr P i j)

end GlobalTheory.Mem.Col2.ChEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExactOfIsAdelicPointOfFramedLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framesExact_of_isAdelicPointOfFramedLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ), (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → ∀ {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}, IsPtOf hc g p → g ∈ UAd hc n ∧ FrExact q g p := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.frExact_of_isPtOf | exact GlobalTheory.Mem.Col2.ChEx.frExact_of_isPtOf | (intros; apply GlobalTheory.Mem.Col2.ChEx.frExact_of_isPtOf <;> assumption)
end
end
