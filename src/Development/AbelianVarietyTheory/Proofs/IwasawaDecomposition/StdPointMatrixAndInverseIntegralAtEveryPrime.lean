module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchTupleChartMemberChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem ptOf_std_entries_intAtA : ∀ {B : Base} (n : ℕ) (g : GA B n) (p : DecoF B.fields.E n ∅ ∅ ∅), PtOf g p → p.deco.1.N = stdLat B.fields.E n → ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin n), IntAtA (F := B.host.F) P ((g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) ∧ IntAtA (F := B.host.F) P (((g⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
  intro B n g p hp hN P r s
  have hlat := hp.lat
  rw [hN] at hlat
  have hint : ∀ x : Fin n → AfE B.host.F B.host.E, x ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) ↔ ∀ i, x i ∈ Formalism.L2.Herm.intAf B.host.F B.host.E := by
    intro x
    exact mem_latS_std x
  have hone : ∀ a : AfE B.host.F B.host.E, a ∈ Formalism.L2.Herm.intAf B.host.F B.host.E → IntAtA (F := B.host.F) P a := by
    intro a ha
    refine ⟨1, ?_, ?_⟩
    · exact P.asIdeal.ne_top_iff_one.mp P.isPrime.ne_top
    · simpa using ha
  have he : ∀ j : Fin n, (Pi.single j 1 : Fin n → AfE B.host.F B.host.E) ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) := by
    intro j
    rw [hint]
    intro i
    by_cases h : i = j
    · subst h; simp [one_mem]
    · simp [Pi.single_apply, h, zero_mem]
  constructor
  · apply hone
    have hx : (g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) *ᵥ Pi.single s 1 ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) := by
      rw [hlat]
      rw [Matrix.mulVec_mulVec]
      have h1 : ((g⁻¹ : GL (Fin n) (AfE B.host.F B.host.E)) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) * (g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [h1, Matrix.one_mulVec]
      exact he s
    have := (hint _).1 hx r
    simpa [Matrix.mulVec_single] using this
  · apply hone
    have hx := (hlat (Pi.single s 1)).1 (he s)
    have := (hint _).1 hx r
    simpa [Matrix.mulVec_single] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime : ∀ {B : Base} (n : ℕ) (g : GA B n) (p : DecoF B.fields.E n ∅ ∅ ∅), PtOf g p → p.deco.1.N = stdLat B.fields.E n → ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin n), IntAtA (F := B.host.F) P ((g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) ∧ IntAtA (F := B.host.F) P (((g⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
  first | exact @GlobalTheory.ptOf_std_entries_intAtA | exact GlobalTheory.ptOf_std_entries_intAtA | (intros; apply GlobalTheory.ptOf_std_entries_intAtA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeLatticeEqCompanionOfAdelicRep
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeLatticeEqCompanionOfAdelicRep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (h : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
      ((y⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Λ := by
  apply le_antisymm
  · rw [Formalism.L2.PairingIndexBounds.F.latAd, Submodule.span_le]
    intro x hx
    exact Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main (F := F) Λ hfin x ((h _).2 hx)
  · intro x hx
    exact Submodule.subset_span ((h _).1 (Submodule.subset_span ⟨x, hx, rfl⟩))

theorem GlobalTheory.Mem.Col2.AdT.mvL_one {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.MainNotions.G.KAat.mvL (1 : GL (Fin N) E) Λ = Λ := by
  ext x
  simp only [Formalism.MainNotions.G.KAat.mvL, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.MainNotions.G.KAat.toLE_apply, Units.val_one, Matrix.one_mulVec, exists_eq_right]

theorem GlobalTheory.Mem.Col2.AdT.sup_dual_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : Deco E n ST SG) (hd : d.Ok) (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal) (hcop : IsCoprime π (cO E π)) :
    d.L ⊔ Ideal.span {cO E π} • Formalism.HermitianLatticesTheory.dual (hStd E n) d.L = d.N := by
  ext x
  rw [GlobalTheory.Mem.Col2.MemLat.mem_N_iff d hd π hmem hcop, Submodule.mem_sup, Submodule.ideal_span_singleton_smul]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact ⟨y, hy, b, hb, rfl⟩
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨y, hy, _, Submodule.smul_mem_pointwise_smul _ _ _ hb, rfl⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ c : (I.stp u a i).Cl, ((I.stp u a i).rep c).1.1.deco.1.N = GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) ((K (chOf c)).y ⟨c, rfl⟩).1 (K (chOf c)).lev.Lb := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K k hR c
  have hsp := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hG := hsp.1
  have hL := (hsp.2.2 u a).1 c
  have hf := (l.lat u a i c).fg
  rw [← hL] at hf
  have hA := (GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS _ _ _ (Module.Finite.iff_fg.2 hf)
      ((K (chOf c)).y_lat ⟨c, rfl⟩)).trans hL
  unfold GlobalTheory.TwU.latCo
  rw [hA, hG]
  unfold Formalism.L2.PairingIndexBounds.F.compan
  rw [GlobalTheory.Mem.Col2.AdT.mvL_one]
  have key := GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual (((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E))
    (fun x => rfl) ((I.stp u a i).rep c).1.1.deco.1.L
  unfold dualL at key
  erw [key]
  have hsep := sepElt_of_ok l.pr u
  have hmem : ∀ P : (B.primes X).vT u, (B.primes X).piT u ∈ P.1.asIdeal := fun P => by
    have := hsep.conj P
    rwa [cO_cO] at this
  exact (GlobalTheory.Mem.Col2.AdT.sup_dual_eq_N ((I.stp u a i).rep c).1.1.deco.1 ((I.stp u a i).rep c).1.1.deco.2 _ hmem (l.pr.piT_cop u)).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeLatticeEqCompanionOfAdelicRepStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representativeLattice_eq_companion_of_adelicRep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ c : (I.stp u a i).Cl, ((I.stp u a i).rep c).1.1.deco.1.N = GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) ((K (chOf c)).y ⟨c, rfl⟩).1 (K (chOf c)).lev.Lb := by
  first | exact @GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo | exact GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo | (intros; apply GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsCompatibleOtherLaterStagesOfSameChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsCompatibleOtherLaterStagesOfSameChoices
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem frame_eq_of_map_eq {D : D7} {V : HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl


set_option maxHeartbeats 8000000 in
theorem lfT_of_same : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs Φ rep Mt l jL t jL' hj
  obtain ⟨tup', tupT', _, _, _, _, _, ⟨ψY, _, _, _⟩, PW', ιW', _, _, _, _⟩ := y'
  obtain ⟨h1, h2, h3, h4⟩ := hs
  obtain rfl : tup' = (by with_unfolding_all exact (y.tup :)) := eq_of_heq h1
  obtain rfl : tupT' = (by with_unfolding_all exact (y.tupT :)) := eq_of_heq h2
  obtain rfl : ψY = (by with_unfolding_all exact (y.PY.ψ :)) := eq_of_heq h3
  have e4 : (fun i => (PW' i).ψ) = (by with_unfolding_all exact ((fun i => (y.PW i).ψ) :)) := eq_of_heq h4
  obtain rfl : PW' = fun i => rowPsi b (y.PW i) :=
    funext fun i => frame_eq_of_map_eq _ _ ((by with_unfolding_all exact ((congrFun e4 i) :)))
  obtain rfl : jL' = (by with_unfolding_all exact (jL :)) := eq_of_heq hj
  letI := alg b iK
  refine ⟨{
    eW := (by with_unfolding_all exact (t.eW :))
    eW_range := fun i => (by with_unfolding_all exact (((t.eW_range i).trans (by rw [wat_eq b R])) :))
    eW_norm := (by with_unfolding_all exact (t.eW_norm :))
    eW_lat := (by with_unfolding_all exact (t.eW_lat :))
    jMj := (by with_unfolding_all exact (t.jMj :))
    jMj_read := (by with_unfolding_all exact (t.jMj_read :))
    jMj_inj := (by with_unfolding_all exact (t.jMj_inj :))
    jMj_range := fun i => (by with_unfolding_all exact (((t.jMj_range i).trans (congrFun (lift_Wc b F y.tupT y.hm y.hTop y.hinj) i)) :))
    jMj_ip := (by with_unfolding_all exact (t.jMj_ip :))
    jMt := (by with_unfolding_all exact (t.jMt :))
    jMt_inj := (by with_unfolding_all exact (t.jMt_inj :))
    jMt_range := (by with_unfolding_all exact (t.jMt_range :))
    jMt_ip := (by with_unfolding_all exact (t.jMt_ip :))
    theta := fun μ hμ i x h w hw1 he hw2 => by
      have hw1' : ((by with_unfolding_all exact (w :)) : (y.L F).AmbW i) ∈ (toLiftReal R F y.tupT y.hm y.hTop y.hinj).MultW i := by
        rw [lift_MultW b F y.tupT y.hm y.hTop y.hinj]; exact (by with_unfolding_all exact (hw1 :))
      have hw2' : (y.L F).eW i ∘ₗ ((by with_unfolding_all exact (w :)) : (y.L F).AmbW i) ∈ (toLiftReal R F y.tupT y.hm y.hTop y.hinj).Wc i := by
        rw [lift_Wc b F y.tupT y.hm y.hTop y.hinj]; exact (by with_unfolding_all exact (hw2 :))
      exact (by with_unfolding_all exact ((t.theta ((μ)) ((hμ)) ((i)) ((x)) ((h)) ((w)) hw1' ((he)) hw2') : _))
    junk := (by with_unfolding_all exact (t.junk :))
    out := (by with_unfolding_all exact (t.out :))
    isot := fun i π v => by
      unfold Hd.prtW
      rw [isotL_eq a b]
      exact (t.isot i π v)
    disj := fun i π π' hne => by
      unfold Hd.prtW
      rw [isotL_eq a b]
      exact (t.disj i π π' hne)
    read := (by with_unfolding_all exact (t.read :)) }, (by with_unfolding_all exact ((HEq.refl t.eW) :)), (by with_unfolding_all exact ((HEq.refl t.jMt) :))⟩

end GlobalTheory.Mem.R3.Rw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsCompatibleOtherLaterStagesOfSameChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  first | exact @GlobalTheory.Mem.R3.Rw.lfT_of_same | exact GlobalTheory.Mem.R3.Rw.lfT_of_same | (intros; apply GlobalTheory.Mem.R3.Rw.lfT_of_same <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGradedLineDivisorsFullFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGradedLineDivisorsFullFlag
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.GradedDiv

section Diag

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K] {O O' : Subring K} {g h : Mat m K}

theorem diag_mul (hg : Par m O g) (hh : Par m O' h) (τ : ι) (i : Fin (m τ)) :
    (g * h) τ i i = g τ i i * h τ i i := by
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h' | h'
  · rw [(hh τ).2.2.2 l i l.2 h', mul_zero]
  · rw [(hg τ).2.2.2 i l i.2 h', zero_mul]

theorem diag_ne_zero (hg : Par m O g) (τ : ι) (i : Fin (m τ)) : g τ i i ≠ 0 := by
  have := diag_mul hg hg.inv τ i
  rw [Mat.mul_inv hg.det_ne] at this
  exact left_ne_zero_of_mul_eq_one (this.symm.trans (Matrix.one_apply_eq i))

end Diag

theorem exists_div {F : Type} [Field F] {Y : GlobalTheory.ProjVar.Var F} {ι : Type} {m : ι → ℕ} (S : Fr (ratOf Y) m m)
    {A₀ : Mat m Y.Fn} (h₀ : A₀ ∈ S.S (genericPoint Y.X)) :
    ∃ gr : ∀ τ, Fin (m τ) → Y.Dv, ∀ y : Y.X, ∃ A ∈ S.S y, ∃ t : ∀ τ, Fin (m τ) → Y.Fnˣ,
      (∀ τ i, (A₀ * A⁻¹) τ i i = t τ i) ∧ (∀ τ i k, i < k → (A₀ * A⁻¹) τ i k = 0) ∧
        ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  have hP : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y →
      Par m ((ratOf Y).O (genericPoint Y.X)).toSubring (A₀ * A⁻¹) := fun hA =>
    (Fr.mem_iff (Fr.mem_genericPoint hA)).1 h₀
  let t : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y → ∀ τ, Fin (m τ) → Y.Fnˣ := fun hA τ i =>
    Units.mk0 _ (diag_ne_zero (hP hA) τ i)
  have hreg : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      RegAt y ((t hA' τ i : Y.Fn) / t hA τ i) := fun {y A A'} hA hA' τ i => by
    have hg := (Fr.mem_iff hA').1 hA
    have e := diag_mul (hP hA) hg τ i
    rw [← mul_assoc, mul_assoc A₀, Mat.inv_mul (Fr.det_ne hA), mul_one] at e
    have e' : (t hA' τ i : Y.Fn) / t hA τ i = (A * A'⁻¹) τ i i := by
      rw [div_eq_iff (t hA τ i).ne_zero, mul_comm]
      exact e
    rw [e']
    exact mem_O_ratOf.1 ((hg τ).1 i i)
  have hgerm : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      germOf y (t hA τ i) = germOf y (t hA' τ i) := fun {y A A'} hA hA' τ i => by
    rw [germOf_eq_iff, unitAt_iff (div_ne_zero (t hA' τ i).ne_zero (t hA τ i).ne_zero), inv_div]
    exact ⟨hreg hA hA' τ i, hreg hA' hA τ i⟩
  choose A hA using fun y : Y.X => S.nonempty y
  refine ⟨fun τ i => show cartierGroup Y.X from ⟨fun y => germOf y (t (hA y) τ i), fun y => ?_⟩,
    fun y => ⟨A y, hA y, t (hA y), fun _ _ => rfl, fun τ i k hik => (hP (hA y) τ).2.2.2 i k i.2 hik,
      fun _ _ => rfl⟩⟩
  obtain ⟨U, B, hy, hB, hU⟩ := S.loc y
  have hBm : ∀ z ∈ U, B ∈ S.S z := fun z hz => (hU z hz B).2 (by rw [Mat.mul_inv hB]; exact Par.one)
  exact ⟨U, hy, t (hBm y hy) τ i, fun z hz => hgerm (hA z) (hBm z hz) τ i⟩

theorem exists_gr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e Y π f₀ S A₀ hT
  obtain ⟨gr, hgr⟩ := exists_div S hT.1
  refine ⟨gr, fun y => ?_⟩
  obtain ⟨A, hA, t, h1, h2, h3⟩ := hgr y
  obtain ⟨φ, f, hf⟩ := hT.2 y A hA
  exact ⟨φ, f, t, (f.tri_iff _ f₀ t).2 ⟨_, hf, h1, h2⟩, h3⟩

end GlobalTheory.ShFam.GradedDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGradedLineDivisorsFullFlagStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_graded_line_divisors_full_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  first | exact @GlobalTheory.ShFam.GradedDiv.exists_gr | exact GlobalTheory.ShFam.GradedDiv.exists_gr | (intros; apply GlobalTheory.ShFam.GradedDiv.exists_gr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariant
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeoConst

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem phiAt_eq (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ) (f : T.R ((i : ℕ) + 1)) :
    phiAt T i σ hV c f = adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) σ))
      (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) c)
      (rdU (T.U ((i : ℕ) + 1) σ) f) := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W),
      castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) c) (rdU (T.U ((i : ℕ) + 1) σ) f)) =
      adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) c)
        (rdU (T.U ((i : ℕ) + 1) σ) f) := by
    intro W hV
    subst hV
    rfl
  exact key _ hV

theorem eqAt_base (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hL : R.toLevCh.Is A.μ0) (hT : TieIn T R κ v₀) (i : Fin D.R.m) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (h : O.EquivAt (κ i) cc) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) :
    EqAt T R κ O T.σ₀ hV cc := by
  intro g k hk f hf
  obtain ⟨h1, h2⟩ := h g k hk f hf
  obtain ⟨y, hy⟩ := GlobalTheory.ChiDetValues.chiC_mem_coeff T R κ v₀ hL hT i g
  have hy' : D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) =
      ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) := by
    rw [hy, chiC, Units.coe_prod]
  refine ⟨h1, y, hy', fun x => ?_⟩
  have e : T.σ₀ y = D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) :=
    (RingHom.congr_fun (res_embLL T hT.alg hT.laws.pins.2.2.1) y).symm
  rw [phiAt_eq, phiAt_eq, e, hy']
  exact h2 x


set_option maxHeartbeats 1000000 in
theorem exists_constants : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (cc : ∀ i : Fin D.R.m, (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → (∀ i, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (cc i) 1) → ∃ cE, (∀ i : Fin D.R.m, cE ((i : ℕ) + 1) T.σ₀ = cc i) ∧ TieIn (setCE T cE) R κ v₀ ∧ (∀ i, OMPins (setCE T cE) R κ v₀ O i) ∧ Fired (setCE T cE) R κ v₀ O (fun _ => 1) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O cc hL hT hpb hP hO
  have H : ∀ (n : ℕ) (σ : T.Q.c.F →+* ℂ), ∃ c : (T.U (n + 1) σ).Comp → ℂ, CUnit c ∧ ∀ hn : n < D.R.m,
      (σ = T.σ₀ → HEq c (cc ⟨n, hn⟩)) ∧ (GoodEmb T.Q.c σ → ∀ hV : T.V (n + 1) σ = Wc D ⟨n, hn⟩,
        EqAt T R κ (O ⟨n, hn⟩) σ hV c) := by
    intro n σ
    by_cases hn : n < D.R.m
    · by_cases hσ : σ = T.σ₀
      · subst hσ
        exact ⟨cc ⟨n, hn⟩, (hO ⟨n, hn⟩).2.1.2.2.2.1, fun _ => ⟨fun _ => HEq.rfl, fun _ hV =>
          eqAt_base T R κ v₀ hL hT ⟨n, hn⟩ (O ⟨n, hn⟩) (cc ⟨n, hn⟩) (hO ⟨n, hn⟩).1 hV⟩⟩
      · by_cases hg : GoodEmb T.Q.c σ ∧ T.V (n + 1) σ = Wc D ⟨n, hn⟩
        · obtain ⟨c, hc, hE⟩ := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R κ v₀ O hL hT hpb hP ⟨n, hn⟩ σ hg.1 hg.2
          exact ⟨c, hc, fun _ => ⟨fun h => absurd h hσ, fun _ _ => hE⟩⟩
        · exact ⟨fun _ => 1, fun _ => norm_one, fun _ => ⟨fun h => absurd h hσ, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩⟩
    · exact ⟨fun _ => 1, fun _ => norm_one, fun h => absurd h hn⟩
  choose c hc hc' using H
  have h0 : ∀ i : Fin D.R.m, c i T.σ₀ = cc i := fun i => eq_of_heq ((hc' i T.σ₀ i.2).1 rfl)
  refine ⟨fun j => Nat.casesOn (motive := fun j => ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ) j (fun _ _ => 1) c, h0, ?_,
    hP, fun i => ?_, fun i σ hσ hV => (hc' i σ i.2).2 hσ hV⟩
  · refine ⟨{ toLawsM := hT.laws.toLawsM, cUnit := ?_, muVal := hT.laws.muVal, muConj := hT.laws.muConj,
              intAll := hT.laws.intAll, modelW := hT.laws.modelW, familyUniformisationBasePointOrthogonal := hT.laws.familyUniformisationBasePointOrthogonal, kfHalf := hT.laws.kfHalf,
              adPin := hT.laws.adPin }, hT.alg, hT.kap, hT.hv₀, hT.chiR, hT.x0⟩
    intro j _ σ _
    cases j with
    | zero => exact fun _ => norm_one
    | succ n => exact hc n σ
  · have h := hO i
    rw [← h0 i] at h
    exact h

end GlobalTheory.RealGeoConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariantStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_core_constants_base_solution_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (cc : ∀ i : Fin D.R.m, (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → (∀ i, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (cc i) 1) → ∃ cE, (∀ i : Fin D.R.m, cE ((i : ℕ) + 1) T.σ₀ = cc i) ∧ TieIn (setCE T cE) R κ v₀ ∧ (∀ i, OMPins (setCE T cE) R κ v₀ O i) ∧ Fired (setCE T cE) R κ v₀ O (fun _ => 1) := by
  first | exact @GlobalTheory.RealGeoConst.exists_constants | exact GlobalTheory.RealGeoConst.exists_constants | (intros; apply GlobalTheory.RealGeoConst.exists_constants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomain
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem lminor_pos_of_posDef {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) (k : Fin (m + 1)) :
    0 < lminor M k :=
  (h.submatrix (Fin.castLE_injective _)).det_pos

theorem lminor_neg' {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (k : Fin (m + 1)) :
    lminor (-M) k = (-1) ^ (k : ℕ) * lminor M k := by
  unfold lminor
  rw [submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg, Fintype.card_fin]

theorem psgn_of_le' {q i : ℕ} (h : i ≤ q) : psgn q i = 1 :=
  Finset.prod_eq_one fun a ha => by
    have := Finset.mem_range.1 ha
    simp [sgn, show a < q by omega]

theorem psgn_add' (q k : ℕ) : psgn q (q + k) = (-1) ^ k := by
  induction k with
  | zero => simpa using psgn_of_le' (le_refl q)
  | succ k ih =>
    have : psgn q (q + (k + 1)) = psgn q (q + k) * sgn q (q + k) := Finset.prod_range_succ _ _
    rw [this, ih]
    simp [sgn, pow_succ]

theorem signs_of_blocks {r p q : ℕ} {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (H : Matrix (Fin r) (Fin r) ℂ)
    (h2 : (reindex e e H).toBlocks₂₂.PosDef) (hs : (-schur (reindex e e H)).PosDef) (i : Fin (r + 1)) :
    0 < psgn q i * (lminor H i).re := by
  obtain ⟨h₁, h₂⟩ := GlobalTheory.FlagFibre.lminor_block r p q e he H h2.det_pos.ne'.isUnit
  have hr := he.card
  by_cases hi : (i : ℕ) ≤ q
  · rw [psgn_of_le' hi, one_mul, h₁ i ⟨i, by omega⟩ rfl]
    exact (Complex.pos_iff.1 (lminor_pos_of_posDef h2 _)).1
  · have hi2 := i.2
    obtain ⟨k, hk⟩ : ∃ k : Fin (p + 1), (i : ℕ) = q + k := ⟨⟨i - q, by omega⟩, by simp only; omega⟩
    have h3 := mul_pos h2.det_pos (lminor_pos_of_posDef hs k)
    rw [lminor_neg'] at h3
    rw [h₂ i k hk, hk, psgn_add', ← Complex.re_ofReal_mul]
    have h4 := (Complex.pos_iff.1 h3).1
    convert h4 using 2
    push_cast
    ring

theorem signs_over_dom : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ),
    reindex e e A = -Jpq p q → ∀ y : Low r → ℂ, toMat (base e y) ∈ hcDom p q →
    ∀ i : Fin (r + 1), 0 < psgn q i * (lminor ((uni y)ᴴ * A * uni y) i).re := by
  intro r p q e he A hA y hy i
  obtain ⟨w, rfl⟩ := glue_surjective he y
  rw [base_glue he] at hy
  have hy' : (1 - (toMat w.1)ᴴ * toMat w.1).PosDef := hy
  have hinj : ∀ {m : ℕ} (u : Low m → ℂ), Function.Injective (uni u).mulVec := fun u =>
    mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (by rw [det_uni]; exact isUnit_one))
  set Z := toMat w.1 with hZ
  set a := uni w.2.2 with ha
  set b := uni w.2.1 with hb
  have hH : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      fromBlocks (-(aᴴ * a)) (-(aᴴ * Z * b)) (-(aᴴ * Z * b))ᴴ (bᴴ * (1 - Zᴴ * Z) * b) := by
    have : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
        (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w)) := by
      simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [this, reindex_uni_glue he, hA, Jpq, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply]
    congr 1
    · simp [ha]
    · simp [ha, hb, hZ, Matrix.mul_assoc]
    · simp [ha, hb, hZ, Matrix.mul_assoc]
    · simp [hb, hZ, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, sub_eq_neg_add]
  have h2 : (bᴴ * (1 - Zᴴ * Z) * b).PosDef := hy'.conjTranspose_mul_mul_same (hinj _)
  refine signs_of_blocks he _ ?_ ?_ i
  · rw [hH, toBlocks_fromBlocks₂₂]; exact h2
  · rw [hH, schur, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      neg_sub, sub_neg_eq_add, add_comm]
    refine PosDef.add_posSemidef ?_ (h2.inv.posSemidef.mul_mul_conjTranspose_same _)
    simpa using (PosDef.one (n := Fin p) (R := ℂ)).conjTranspose_mul_mul_same (hinj w.2.2)

end GlobalTheory.FlagFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomainStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ y : Low r → ℂ, toMat (base e y) ∈ hcDom p q → ∀ i : Fin (r + 1), 0 < psgn q i * (lminor ((uni y)ᴴ * A * uni y) i).re := by
  first | exact @GlobalTheory.FlagFibre.signs_over_dom | exact GlobalTheory.FlagFibre.signs_over_dom | (intros; apply GlobalTheory.FlagFibre.signs_over_dom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingGlueLowerUnitriangularBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingGlueLowerUnitriangularBlocks
noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q : ℕ}

def lowPos {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : (Fin p × Fin q) ⊕ Low q ⊕ Low p → Low r
  | .inl s => ⟨(e.symm (.inl s.1), e.symm (.inr s.2)), by
      rw [Fin.lt_def]; simp only [he.1, he.2]; have := s.2.2; omega⟩
  | .inr (.inl s) => ⟨(e.symm (.inr s.1.1), e.symm (.inr s.1.2)), by
      rw [Fin.lt_def]; simp only [he.2]; exact s.2⟩
  | .inr (.inr s) => ⟨(e.symm (.inl s.1.1), e.symm (.inl s.1.2)), by
      rw [Fin.lt_def]; simp only [he.1]; have : (s.1.2 : ℕ) < s.1.1 := s.2; omega⟩

theorem lowPos_bijective {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : Function.Bijective (lowPos he) := by
  constructor
  · rintro (⟨a, b⟩ | ⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩) (⟨c, d⟩ | ⟨⟨c, d⟩, h'⟩ | ⟨⟨c, d⟩, h'⟩) hx <;>
      simp_all [lowPos]
  · rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    obtain ⟨b, rfl⟩ := e.symm.surjective b
    have h : (e.symm b : ℕ) < e.symm a := hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at h
    · exact ⟨.inr (.inr ⟨(a, b), by rw [Fin.lt_def]; simp only; omega⟩), rfl⟩
    · exact ⟨.inl (a, b), rfl⟩
    · have := a.2; omega
    · exact ⟨.inr (.inl ⟨(a, b), h⟩), rfl⟩

theorem measurePreserving_mul_uni (y : Low q → ℂ) :
    MeasurePreserving (fun v : Fin p × Fin q → ℂ => vecOf (toMat v * uni y)) volume volume := by
  have hc : Continuous fun v : Fin p × Fin q → ℂ => vecOf (toMat v * uni y) :=
    continuous_pi fun s => (continuous_toMat.matrix_mul continuous_const).matrix_elem s.1 s.2
  refine ⟨hc.measurable, Measure.ext fun s hs => ?_⟩
  have h := GlobalTheory.FlagFibre.lintegral_affine p q 1 (uni y) 0 (by simp) (by simp [det_uni]) (s.indicator 1)
    (measurable_one.indicator hs)
  simp only [Matrix.one_mul, add_zero, det_uni, det_one, map_one, one_pow, mul_one, inv_one,
    ENNReal.ofReal_one, one_mul] at h
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, lintegral_map (measurable_one.indicator hs) hc.measurable, h]

theorem measurePreserving_shear_uni :
    MeasurePreserving (fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) =>
      (vecOf (toMat w.1 * uni w.2.1), w.2)) volume volume := by
  have hc : Continuous (Function.uncurry fun (y : (Low q → ℂ) × (Low p → ℂ)) (v : Fin p × Fin q → ℂ) =>
      vecOf (toMat v * uni y.1)) :=
    continuous_pi fun s => ((continuous_toMat.comp continuous_snd).matrix_mul
      (continuous_uni.comp (continuous_fst.comp continuous_fst))).matrix_elem s.1 s.2
  have h := (MeasurePreserving.id (volume : Measure ((Low q → ℂ) × (Low p → ℂ)))).skew_product
    (μc := volume) (μd := volume) hc.measurable
    (Filter.Eventually.of_forall fun y => (measurePreserving_mul_uni y.1).map_eq)
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

theorem measurePreserving_glue (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q) (he : IsBlockSL2Embedding e) :
    MeasurePreserving (glue e) volume volume := by
  let σ := Equiv.ofBijective _ (lowPos_bijective he)
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : Low r => ℂ) σ
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin p × Fin q) ⊕ Low q ⊕ Low p => ℂ)
  have h3 := (MeasurePreserving.id (volume : Measure (Fin p × Fin q → ℂ))).prod
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Low q ⊕ Low p => ℂ))
  have h := h1.comp (h2.comp (h3.comp measurePreserving_shear_uni))
  convert h using 1
  funext w s
  obtain ⟨x, rfl⟩ := σ.surjective s
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rcases x with ⟨a, b⟩ | ⟨⟨a, b⟩, hab⟩ | ⟨⟨a, b⟩, hab⟩
  · simp only [σ, Equiv.ofBijective_apply, lowPos, glue, Equiv.apply_symm_apply, fromBlocks_apply₁₂]
    rfl
  · have hab' : b < a := hab
    simp only [σ, Equiv.ofBijective_apply, lowPos, glue, Equiv.apply_symm_apply, fromBlocks_apply₂₂, uni,
      of_apply, dif_pos hab']
    rfl
  · have hab' : b < a := hab
    simp only [σ, Equiv.ofBijective_apply, lowPos, glue, Equiv.apply_symm_apply, fromBlocks_apply₁₁, uni,
      of_apply, dif_pos hab']
    rfl

end GlobalTheory.FlagFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingGlueLowerUnitriangularBlocksStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → MeasurePreserving (glue e) volume volume := by
  first | exact @GlobalTheory.FlagFibre.measurePreserving_glue | exact GlobalTheory.FlagFibre.measurePreserving_glue | (intros; apply GlobalTheory.FlagFibre.measurePreserving_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourierJacobiConstantTermEqZeroOfFlowLine
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourierJacobiConstantTermEqZeroOfFlowLine
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom Filter Topology

namespace GlobalTheory.CuspLimit


open Classical in
theorem tendsto_dirichlet {ι : Type*} (A : ι → ℂ) (a : ι → ℝ) (F : ℝ → ℂ) (T : ℝ)
    (ha : ∀ i, A i ≠ 0 → 0 ≤ a i)
    (hs : ∀ t, T < t → HasSum (fun i => A i * (Real.exp (-(a i * t)) : ℂ)) (F t)) :
    Tendsto F atTop (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
  have h0 : Summable fun i => ‖A i * (Real.exp (-(a i * (T + 1))) : ℂ)‖ :=
    (hs (T + 1) (by linarith)).summable.norm
  have hlim : Tendsto (fun t : ℝ => ∑' i, A i * (Real.exp (-(a i * t)) : ℂ)) atTop
      (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
    refine tendsto_tsum_of_dominated_convergence h0 (fun i => ?_) ?_
    · by_cases hi : A i = 0
      · simp [hi]
      by_cases hz : a i = 0
      · simp [hz]
      have hp : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hz)
      rw [if_neg hz]
      have h1 : Tendsto (fun t : ℝ => Real.exp (-(a i * t))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hp)
      have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).const_mul (A i)
      simpa using h2
    · filter_upwards [eventually_ge_atTop (T + 1)] with t ht i
      by_cases hi : A i = 0
      · simp [hi]
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      exact neg_le_neg (mul_le_mul_of_nonneg_left ht (ha i hi))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop T] with t ht
  exact (hs t ht).tsum_eq

theorem fj_zero_eq_zero_of_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  intro E _ _ _ r X la P ξ x s d T g hP hnn hξ hx hd hg hw
  classical
  have hpi := Real.pi_pos
  set F : ℝ → ℂ := fun t => P (X.flow ξ (fun τ => s τ + (I * t) * (d τ : ℂ)) x) with hF
  have him : ∀ t : ℝ, T < t → T < (I * (t : ℂ)).im := fun t ht => by simpa using ht
  have h1 := tendsto_dirichlet g (fun m : ℤ => 2 * Real.pi * m) F T
    (fun m hm => by
      have : 0 < m := by
        by_contra h
        exact hm (hg m (not_lt.mp h))
      positivity)
    (fun t ht => by
      have h := (hw _ (him t ht)).2
      convert h using 3 with m
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi, ← Complex.exp_int_mul]
      push_cast
      congr 1
      linear_combination (-(2 * (Real.pi : ℂ) * m * t)) * Complex.I_mul_I)
  have e1 : (∑' m : ℤ, if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = 0 := by
    have : (fun m : ℤ => if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = fun _ => 0 := by
      funext m
      split_ifs with h
      · have hm : m = 0 := by simpa [hpi.ne'] using h
        exact hg m hm.le
      · rfl
    rw [this, tsum_zero]
  have h2 := tendsto_dirichlet
    (fun ν : X.Ψ → ℝ => X.fj la ξ ν P x * cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ))
    (fun ν => 4 * Real.pi * ∑ τ, ν τ * d τ) F T
    (fun ν hν => by
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hν)
      have : 0 ≤ ∑ τ, ν τ * d τ := Finset.sum_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le
      positivity)
    (fun t ht => by
      have h := m3bExp_holds r X la P hP ξ hξ x hx _ (hw _ (him t ht)).1
      convert h using 2 with ν
      rw [mul_assoc]
      congr 1
      push_cast
      rw [← Complex.exp_add]
      congr 1
      have e : ∑ τ, (ν τ : ℂ) * (s τ + I * t * (d τ : ℂ)) =
          ∑ τ, (ν τ : ℂ) * s τ + I * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun τ _ => by ring
      rw [e]
      linear_combination (-(4 * (Real.pi : ℂ) * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ))) * Complex.I_mul_I)
  rw [tsum_eq_single (0 : X.Ψ → ℝ) (fun ν hν => by
    split_ifs with h
    · by_contra hne
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hne)
      have hz : ∑ τ, ν τ * d τ = 0 := by simpa [hpi.ne'] using h
      refine hν (funext fun τ => ?_)
      have := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le).mp hz τ
        (Finset.mem_univ τ)
      exact (mul_eq_zero.mp this).resolve_right (hd τ).ne'
    · rfl)] at h2
  rw [e1] at h1
  simpa using tendsto_nhds_unique h2 h1

end GlobalTheory.CuspLimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourierJacobiConstantTermEqZeroOfFlowLineStatement
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  first | exact @GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line | exact GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line | (intros; apply GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainMiddleStageChartsJoinedMember
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberChartMatchingAwayFromTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberChartMatchingAwayFromTwist
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw


set_option maxHeartbeats 8000000 in
theorem match_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → ∀ (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∃ (g : Chart I u a i → Ch0) (k : Chart I u a i → GA B (B.R.N i)), AdmK I u a i k ∧ ∀ β, ∃ c, chartOf I u a i c = β ∧ ∃ c0, chOf0 c0 = g β ∧ ∀ x : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) x = 1) → (∀ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ → ∃ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr c0.1 κ0) ∧ (∀ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 → ∃ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ) := by
  intro B X I hI hP l u a Q i hi Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 h1 h2 hQ hR0
  obtain ⟨c0f, t, ht1, ht2, ht3, hM⟩ := GlobalTheory.T.match_tupleChart_memberChart I hI hP l u a Q i hi h1 h2 hQ
  refine ⟨fun β => chOf0 (c0f β), fun β => k0 (chOf0 (c0f β)) * t β,
    GlobalTheory.T.admissibleBasePoint_chart_mul_twist_alt I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR0 _ t ht1 ht2 ht3, ?_⟩
  intro β
  obtain ⟨c, hc, hs⟩ := hM β
  refine ⟨c, hc, c0f β, rfl, ?_⟩
  intro x hx
  have e : (k0 (chOf0 (c0f β)) * t β)⁻¹ * x * (k0 (chOf0 (c0f β)) * t β) =
      (t β)⁻¹ * ((k0 (chOf0 (c0f β)))⁻¹ * x * k0 (chOf0 (c0f β))) * t β := by group
  rw [e]
  refine hs _ fun v hv => ?_
  rw [map_mul, map_mul, hx v hv, mul_one, map_inv, inv_mul_cancel]


set_option maxHeartbeats 8000000 in
theorem charts_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k ∧ ∀ (K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k → ∀ β, (∀ κ : (K β).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → ∃ h' : κ.1 ∈ (K0 (g β)).lev.U, (K β).lev.chi κ = (K0 (g β)).lev.chi ⟨κ.1, h'⟩) ∧ ∀ κ' : (K0 (g β)).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = 1) → κ'.1 ∈ (K β).lev.U := by
  intro B X I hI hP l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR0
  obtain ⟨k0, hk0⟩ := hR0
  obtain ⟨g, k, hk, hM⟩ := match_base I hI hP l u a Q i hi Ch0 chOf0 _ _ _ _ _ k0 h1 h2 hQ hk0
  refine ⟨g, k, hk, ?_⟩
  intro K hK β
  obtain ⟨c, hc, c0, hc0, hx⟩ := hM β
  subst hc
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have huni : ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (B.T u) (I.rec7 l Z).R.f bad) (x : GA B (B.R.N i)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) := by
    intro bad S x hx
    have h := ((S.U_eq x).1 hx).1
    rw [hgram] at h
    exact h
  have hnQ0 : ∀ v, ¬ I.UnderQ I.mu0 v := by
    rintro v ⟨P, hP, -⟩
    rw [ColIn.twistPrimes_reference_tuple_eq_empty] at hP
    exact absurd hP (Finset.notMem_empty _)
  refine ⟨fun κ hκ => ?_, fun κ' hκ' => ?_⟩
  · obtain ⟨κ1, hl1⟩ := GlobalTheory.T.chartLevel_twistTrivial_localMove I hI l u a i hi _ _ _ _ _ _ k hK c κ.1 (huni _ κ.1 κ.2)
      (fun v hv => hκ v ((hQ v).2 hv)) κ.2
    obtain ⟨κ0, hl0, hchr⟩ := (hx κ.1 hκ).1 κ1 hl1
    obtain ⟨hm0, hc0'⟩ := reads_of_locMv I hI hk0 c0 κ.1 κ0 (by rw [hc0]; exact hl0)
    obtain ⟨hm, hcc⟩ := reads_of_locMv I hI hK c κ.1 κ1 hl1
    have key : ∀ β0 (e : chOf0 c0 = β0), ∃ h' : κ.1 ∈ (K0 β0).lev.U,
        (((K0 β0).lev.chi ⟨κ.1, h'⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 i).chr c0.1 κ0 : B.LLˣ) : B.LL) := by
      intro β0 e
      subst e
      exact ⟨hm0, hc0'⟩
    obtain ⟨h', e'⟩ := key _ hc0
    refine ⟨h', Units.ext ?_⟩
    rw [e', ← hchr]
    exact hcc
  · have hm0 : κ'.1 ∈ (K0 (chOf0 c0)).lev.U := by rw [hc0]; exact κ'.2
    obtain ⟨κ0, hl0⟩ := GlobalTheory.T.chartLevel_twistTrivial_localMove I hI l u I.mu0 i hi _ _ _ _ _ _ k0 hk0 c0 κ'.1 (huni _ κ'.1 hm0)
      (fun v hv => absurd hv (hnQ0 v)) hm0
    rw [hc0] at hl0
    obtain ⟨κ, hl⟩ := (hx κ'.1 hκ').2 κ0 hl0
    exact (reads_of_locMv I hI hK c κ'.1 κ hl).1

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberChartMatchingAwayFromTwistStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_memberChart_matching_awayFromTwist : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k ∧ ∀ (K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k → ∀ β, (∀ κ : (K β).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → ∃ h' : κ.1 ∈ (K0 (g β)).lev.U, (K β).lev.chi κ = (K0 (g β)).lev.chi ⟨κ.1, h'⟩) ∧ ∀ κ' : (K0 (g β)).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = 1) → κ'.1 ∈ (K β).lev.U := by
  intro B X I hI pins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hK
  exact GlobalTheory.Mem.Col2.TC.ChTw.charts_match I hI pins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainMiddleStageChartsJoinedMember
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.ChTw


set_option maxHeartbeats 1000000 in
theorem charts_tuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (g : Ch → Ch0), I.ReadsK l Z u a i hi chOf K ∧ ∀ β, (∀ v, v ∉ Q → (K β).lev.Uloc v = (K0 (g β)).lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K β).lev.U) (κ' : (K0 (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = (K0 (g β)).lev.chi κ' := by
  set_option maxHeartbeats 0 in
    intro B X I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR
    have h := GlobalTheory.T.exists_memberChart_matching_awayFromTwist I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ
    have hresult := h (by exact hR)
    obtain ⟨g, k, hk, hC⟩ := hresult
    have hB := GlobalTheory.T.exists_finiteOrder_charts_middle_steps I hok hpins l Z u a Q i hi h1 h2 hQ k hk
    obtain ⟨K, hKB⟩ := hB
    have hK := hKB.1
    have hfin := hKB.2
    have hCK := hC K hK
    haveI := finite_chart I l u a i
    refine ⟨Chart I u a i, inferInstance, chartOf I u a i, K, g, ⟨k, hK⟩, fun β => ⟨?_, hfin β, ?_⟩⟩
    · intro v hv
      refine GlobalTheory.T.stepLevel_localGroup_eq_of_agree_off_places (K β).lev (K0 (g β)).lev (Q : Set _) (fun x hx => ⟨fun hxK => ?_, fun hx0 => ?_⟩) v hv
      · exact ((hCK β).1 ⟨x, hxK⟩ hx).1
      · exact (hCK β).2 ⟨x, hx0⟩ hx
    · intro κ κ' he hq
      obtain ⟨h', e⟩ := (hCK β).1 κ hq
      exact e.trans (congrArg (K0 (g β)).lev.chi (Subtype.ext he))

end GlobalTheory.Mem.Col2.TC.ChTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainMiddleStageChartsJoinedMemberStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleChain_middleStage_charts_joined_member : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (g : Ch → Ch0), I.ReadsK l Z u a i hi chOf K ∧ ∀ β, (∀ v, v ∉ Q → (K β).lev.Uloc v = (K0 (g β)).lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K β).lev.U) (κ' : (K0 (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = (K0 (g β)).lev.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.charts_tuple | exact GlobalTheory.Mem.Col2.TC.ChTw.charts_tuple | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.charts_tuple <;> assumption)
end
end
