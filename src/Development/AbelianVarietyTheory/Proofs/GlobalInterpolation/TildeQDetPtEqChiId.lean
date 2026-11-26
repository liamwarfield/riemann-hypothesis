module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MkDetPtEqRelDetQ
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntOfHomAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommonRepresentativesPeriodLatticeHalves

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.ChiDet

theorem tildeQ_detPt_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ) (C : GlobalTheory.Mem.Chr.HFrame H e) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))), letI := H.cmStar; ∀ (p : DecoF H.E n ST SG Q), LevOk H SG SQ → ((tildeQ H SQ C.chiPsi (detPt H SQ p) : ℂˣ) : ℂ) = chiId C.chiPsi (Th.detId H (Th.stdL H n) p.deco.1.N) := by
  intro R H e C n ST SG Q SQ
  letI := H.cmStar
  intro p hL
  have hχ := C.isChi
  have hK := (GlobalTheory.Mem.KerDet.kernel_open_and_factor R H).2.2.2 C.chiPsi hχ.triv (fun v y hy _ => hχ.unr v y hy)
    fun v _ => hχ.unr v
  rw [tildeQ_eq_comp H SQ hK, MonoidHom.comp_apply]
  exact tildeD_eq_chiId R H C.chiPsi hχ n _ p.deco.2.lat _
    (congrArg (toDtTMod H SQ) (mk_detPt_eq_relDetQ R H n ST SG Q SQ p hL))

end GlobalTheory.Mem.ChiDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GenusMassAtTwo
namespace GlobalTheory

theorem genusMassAt_two : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2 :=
  fun D => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.genusMassAt_of D (genusMassStd_all D) 2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatStepOfChThOk
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.KerT

theorem ratStep_of_chTh_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2) → i < R.m → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i (i + 1) := by
  intro X Pr R W Ch sel S mu cst L G m2 u i A _ _ _ _ _ _ hL _ hT hi
  have hq := Formalism.L2.Ker.muqTie_of_ok Ch sel mu cst L hL
  have hm := hL.hm
  have key : ∀ j, (j = i + 1 ∧ i ≤ m2) ∨ (j = R.m ∧ i = m2 + 1) → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i j := by
    intro j hj
    unfold RatStep
    rw [← Formalism.L2.Ker.stepC_eq_stepT W Ch sel mu cst hq A u i hi]
    rcases hj with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
    · intro γ γ' N fr N' fr' c x h'
      exact (hT.th i h).equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
    · intro γ γ' N fr N' fr' c x h'
      exact hT.top.equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
  exact key _ (by omega)

end GlobalTheory.KerT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DecoratedLatticePointMoveDiamond
noncomputable section

namespace GlobalTheory.LvT.Built

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem levelPrimeDatum_diamond_invariant {E : Type} [Field E] [NumberField E] [StarRing E] (K : Type) [Field K] {n n' : ℕ}
    {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (d' : DecoSet (E := E) (n := n') (ST := ST) (SG := SG')) (P : ST)
    (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) : phiT K (DecoSet.dia1 P a d).1 (DecoSet.dia1 P a d').1 = phiT K d.1 d'.1 := by
  funext x
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
  refine forall_congr' fun Q => forall_congr' fun y => ?_
  refine imp_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [DecoSet.dia1, DecoSet.dia, Deco.dia]
  exact Units.mul_right_inj _

theorem decoratedLatticePoint_move_diamond {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (p : PtY ST SG Q y) (P : ST)
    (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.deco = DecoSet.dia1 P a p.1.1.deco ∧
      (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.fr = p.1.1.fr ∧ (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.2 = p.1.2 := by
  have h : p.mv (DecoSet.dia1 P a p.1.1.deco) =
      ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ := dif_pos ⟨p.1.1.2, p.2⟩
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

theorem kAt_dia : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → ∀ b b' d d' (P : Pr.vT u) a, kAt W Ch sel mu cst L A u i b b' ((tdatAt sel mu cst L Tp u i).dia b P a d) ((tdatAt sel mu cst L Tp u (i + 1)).dia b' P a d') = kAt W Ch sel mu cst L A u i b b' d d' := by
  intro X Pr R W Ch sel S mu cst L G m2 u i _ _ _ _ _ Tp A h b b' d d' P a
  obtain ⟨Ξ, -, -, -, -, h⟩ := h b b' d d'
  have key : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p (p.mv (DecoSet.dia1 P a p.1.1.deco)) := by
    intro j p
    obtain ⟨h1, h2, h3⟩ := decoratedLatticePoint_move_diamond p P a
    refine ⟨?_, ?_, h2.symm, h3.symm⟩
    · rw [h1]; exact fun _ _ => rfl
    · rw [h1]; rfl
  have h0 := h d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have h1 := h _ _ (key d) (key d')
  refine h1.trans (Eq.trans ?_ h0.symm)
  rw [(decoratedLatticePoint_move_diamond d P a).1, (decoratedLatticePoint_move_diamond d' P a).1]
  unfold GlobalTheory.KerT.term
  rw [levelPrimeDatum_diamond_invariant]
  rfl

end GlobalTheory.LvT.Built
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugatePrimeBoundPointKernelOfCoefficientKerne
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugatePrimeBoundPointKernelOfCoefficientKerne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.BarPass

variable {D : D7} {u : D.what₂.Word}

theorem valB_smul_eq {X : Ch D u} {i : ℕ} {M : PtModel X i} (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT)
    (g : M.G) (hg : ∀ v, M.loc v g = 1) (p : M.Pt) : Co.valB w V (g • p) = Co.valB w V p := by
  have h : ∀ v, (g • p).2 v = p.2 v := by
    intro v
    have h1 := M.smul_snd g p v
    rw [hg v] at h1
    apply Subtype.ext
    apply LocF.Raw.ext
    · ext x
      simpa using (h1 x).1
    · funext x
      simpa using (h1 x).2
  unfold PtModel.Coord.valB
  simp only [h]

variable {B : Built.Dat D u} {i : ℕ}

theorem ev_smul (c : D.what₂.LL) (F : B.V i) : B.ev i (c • F) = D.what₂.embLL c • B.ev i F :=
  LinearMap.map_smulₛₗ (evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL) c F

theorem isIntegral_torsion {L : Type} [Field L] (ζ : CommGroup.torsion Lˣ) : IsIntegral ℤ ((ζ.1 : Lˣ) : L) := by
  obtain ⟨n, hn, h⟩ := (isOfFinOrder_iff_pow_eq_one).1 ((CommGroup.mem_torsion _).1 ζ.2)
  refine IsIntegral.of_pow hn ?_
  rw [← Units.val_pow_eq_pow_val, h]
  exact isIntegral_one

theorem act_zeta_mem {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M) {Co : M.Coord}
    (hV : R.ValIs Co) {w : D.what₂.places.Pl} (hw : OverT B.ch w) (b) (d : (B.I.S i).D b) (ζ) (y : M.Val)
    (hy : y ∈ Co.valB w ∅ (R.pt b d)) : M.act (R.zeta ζ) y ∈ Co.valB w ∅ (R.pt b d) := by
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y).1 hy
  refine (hV.dual w hw b d _).2 ⟨((ζ.1 : (D.what₂.LL)ˣ) : D.what₂.LL) • F, ?_, ?_⟩
  · exact (B.valAt w i _).smul_mem (⟨_, isIntegral_torsion ζ⟩ : 𝓞 D.what₂.LL) hF
  · rw [R.act_zeta, ev_smul, ← hyF]
    rfl

theorem intBar_of_kerBar : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerBar k → K.IntBar Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK _ _ hV hV' hb w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  rw [valB_smul_eq Co w ∅ _ (R.loc_zeta ζ)] at hy
  rw [valB_smul_eq Co' w ∅ _ (R'.loc_zeta ζ')]
  have hy0 := act_zeta_mem R hV hw b d ζ⁻¹ y hy
  have hyy : y = M.act (R.zeta ζ) (M.act (R.zeta ζ⁻¹) y) := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
  generalize M.act (R.zeta ζ⁻¹) y = y₀ at hy0 hyy
  obtain ⟨F, hF, hyF⟩ := (hV.dual w hw b d y₀).1 hy0
  obtain ⟨F', hF', hk⟩ := hb w hw hs b b' d d' F hF
  have hm : B.ev (i + 1) F' ∈ M'.Val := by
    rw [R'.val_eq]
    exact evV_mem_ValC B.emb 1 _ D.what₂.embLL F'
  have h1 : (⟨_, hm⟩ : M'.Val) ∈ Co'.valB w ∅ (R'.pt b' d') := (hV'.dual w hw b' d' _).2 ⟨F', hF', rfl⟩
  refine ⟨_, act_zeta_mem R' hV' hw b' d' ζ' _ h1, ?_⟩
  rw [hyy, K.src, hT, ← map_smul]
  congr 1
  apply Subtype.ext
  rw [hK b b' d d' F y₀ hyF, hk, ev_smul, map_pow, map_natCast]
  rfl

end GlobalTheory.LvT.Built.BarPass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugatePrimeBoundPointKernelOfCoefficientKerneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatePrimeBound_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerBar k → K.IntBar Co Co' := by
  first | exact @GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar | exact GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar | (intros; apply GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimitiveRootsCoeffFieldTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ColRootsExistsPrimitiveRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsPrimitiveRootOfAddCharNeOne
namespace GlobalTheory

theorem exists_isPrimitiveRoot_of_addChar_ne_one :
    ∀ (R K : Type) [CommRing R] [Field K] (p : ℕ), p.Prime → (p : R) = 0 →
      ∀ ψ : AddChar R K, ψ ≠ 1 → ∃ ζ : K, IsPrimitiveRoot ζ p := by
  intro R K _ _ p hp hpR ψ hψ
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  have hpow : ψ x ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hpR, zero_mul, AddChar.map_zero_eq_one]
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (ψ x) = p := orderOf_eq_prime hpow hx
  exact ⟨ψ x, hord ▸ IsPrimitiveRoot.orderOf (ψ x)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsPrimitiveRootOfInjectiveCharacter
namespace GlobalTheory

theorem exists_isPrimitiveRoot_of_injective_character (K : Type) [Field K] (p : ℕ) (hp : p.Prime)
    (om : (ZMod p)ˣ →* Kˣ) (hom : Function.Injective om) :
    ∃ ζ : K, IsPrimitiveRoot ζ (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  refine ⟨(om g : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hg, ← orderOf_injective om hom g]
  exact IsPrimitiveRoot.orderOf _

end GlobalTheory
end

open Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory

theorem colRoots_mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A}
    {P : HeightOneSpectrum A} (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hfin
  · exact (Set.Finite.mem_toFinset hfin).mp h
  · exact absurd h (Finset.notMem_empty P)

theorem colRoots_exists_primitiveRoots (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m)
    (hf : 0 < X.f) (hP : Pr.Ok) (hC : Ch.Ok) (i : Fin 2) :
    (∃ ζ : X.K, IsPrimitiveRoot ζ (Pr.g i)) ∧ ∃ ζ : X.K, IsPrimitiveRoot ζ (Pr.g i - 1) := by
  refine ⟨?_, ?_⟩
  · have hcard : 0 < (Pr.vG i).card := by rw [hP.vG_card i]; exact hf
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hcard
    have hwG : w ∈ Pr.vGs := by
      classical
      rw [Primes.vGs, Finset.mem_union]
      fin_cases i
      · exact Or.inl hw
      · exact Or.inr hw
    have hconj : X.conjO (Pr.piG i) ∈ w.asIdeal := colRoots_mem_of_mem_divs hw
    have hg : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
      rw [← hP.piG_norm i]
      exact w.asIdeal.mul_mem_left _ hconj
    have hzero : ((Pr.g i : ℕ) : 𝓞 X.E ⧸ w.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk w.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hg
    exact exists_isPrimitiveRoot_of_addChar_ne_one (𝓞 X.E ⧸ w.asIdeal) X.K (Pr.g i)
      (hP.g_prime i) hzero (Ch.psi0 ⟨w, hwG⟩) (hC.psi_zero_nontrivial_character _)
  · obtain ⟨om, hom, -⟩ := hC.chi_om i
    exact exists_isPrimitiveRoot_of_injective_character X.K (Pr.g i) (hP.g_prime i) om hom

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimitiveRootsCoeffFieldTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem trueCols_exists_primitiveRoots : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : Fin 2), (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧ ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) := by
  intro B X I h l Z i
  have hP := (base_fields_primes_ok B X).2.1
  have hf : 0 < B.fields.f := by
    have e : B.fields.f = 2 * B.R.ord := B.fields_f
    have := B.R.ord_pos
    rw [e]; omega
  exact colRoots_exists_primitiveRoots B.fields (B.primes X) B.R.m I.Ch hf hP h.ch_ok i

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimitiveRootsCoeffFieldTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitiveRoots_coeffField_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : Fin 2), (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧ ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) := by
  first | exact @GlobalTheory.trueCols_exists_primitiveRoots | exact GlobalTheory.trueCols_exists_primitiveRoots | (intros; apply GlobalTheory.trueCols_exists_primitiveRoots <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatTermOfRatStep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

noncomputable section

namespace GlobalTheory.KerRat

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem phiT_move {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (h : GLG (E := E) (n := a) (SG := SG)) (h' : GLG (E := E) (n := b) (SG := SG')) (x : HomE E a b) :
    phiT K (d.act γ h) (d'.act γ' h') (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) = phiT K d d' x := by
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ (forall_congr' fun Q => ?_) rfl rfl
  have key : ∀ y, (y ∈ (d.act γ h).at Q.1 → (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) y ∈ (d'.act γ' h').at Q.1 ∧
      (d'.act γ' h').f Q ((γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) y) = (d.act γ h).f Q y) ↔
      (γ.symm y ∈ d.at Q.1 → x (γ.symm y) ∈ d'.at Q.1 ∧ d'.f Q (x (γ.symm y)) = d.f Q (γ.symm y)) := fun y => by
    show (y ∈ localization₂ _ (gmap γ d.N) → γ' (x (γ.symm y)) ∈ localization₂ _ (gmap γ' d'.N) ∧
      d'.f Q (γ'.symm (γ' (x (γ.symm y)))) = d.f Q (γ.symm y)) ↔ _
    rw [mem_localization_gmap, mem_localization_gmap, LinearEquiv.symm_apply_apply]
  refine ⟨fun H y => ?_, fun H y => (key y).2 (H _)⟩
  have := (key (γ y)).1 (H _)
  rwa [LinearEquiv.symm_apply_apply] at this

theorem kerOf_move {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V') (Sa : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') (γ : UF E a) (γ' : UF E b)
    (N : Submodule (𝓞 E) (Sp E a)) (fr fr₂ : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' fr₂' : Frs E b SB)
    (Ξ Ξ₂ : HomE E a b → K)
    (hcong : ∀ x x', x - x' ∈ mulLat cB (homAt Sa N N') → th N fr N' fr' cB x = th N fr N' fr' cB x')
    (heq : ∀ x, th (gmap γ.1 N) fr₂ (gmap γ'.1 N') fr₂' cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) =
      (rho' γ') ∘ₗ (th N fr N' fr' cB x) ∘ₗ (rho γ⁻¹))
    (hΞ : ∀ x z, z ∈ mulLat cB (homAt Sa N N') → Ξ (x + z) = Ξ x)
    (hΞ₂ : ∀ x : HomE E a b, Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = Ξ x) :
    kerOf th Sa cA cB (gmap γ.1 N) fr₂ (gmap γ'.1 N') fr₂' Ξ₂ =
      (rho' γ') ∘ₗ kerOf th Sa cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹) := by
  have hm : ∀ (g : UF E a), rho g ∘ₗ rho g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hm' : ∀ (g : UF E b), rho' g ∘ₗ rho' g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  let φ : (V →ₗ[K] V') ≃+ (V →ₗ[K] V') :=
    { toFun := fun L => rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹
      invFun := fun L => rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ
      left_inv := fun L => by
        have h1 := hm γ⁻¹
        have h2 := hm' γ'⁻¹
        rw [inv_inv] at h1 h2
        show rho' γ'⁻¹ ∘ₗ (rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹) ∘ₗ rho γ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc, h2]; simp
      right_inv := fun L => by
        show rho' γ' ∘ₗ (rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ) ∘ₗ rho γ⁻¹ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hm, ← LinearMap.comp_assoc, hm']; simp
      map_add' := fun L L' => by simp [LinearMap.comp_add, LinearMap.add_comp] }
  have hH := homConjEquiv_mem_homAt Sa γ.1 γ'.1 N N'
  unfold kerOf
  rw [latSum_transport_equiv (homConjEquiv γ.1 γ'.1) (divLat cA (homAt Sa N N')) (mulLat cB (homAt Sa N N')) _ _
    (mem_divLat_equiv_iff _ _ _ hH cA) (mem_mulLat_equiv_iff _ _ _ hH cB)
    (fun x => φ (Ξ x • th N fr N' fr' cB x))]
  · show _ = φ _
    unfold latSum
    rw [φ.map_finsum]
  · intro x x' hx
    have h1 : Ξ x = Ξ x' := by
      have := hΞ x' (x - x') hx
      rwa [add_sub_cancel] at this
    rw [h1, hcong x x' hx]
  · intro x
    show Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) • th _ _ _ _ cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap)
      = rho' γ' ∘ₗ (Ξ x • th N fr N' fr' cB x) ∘ₗ rho γ⁻¹
    rw [heq, hΞ₂, LinearMap.smul_comp, LinearMap.comp_smul]

omit [NumberField E] [StarRing E] in
theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (c D : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat c M ≤ divLat D M := by
  rintro _ ⟨y, hy, rfl⟩
  show (D : 𝓞 E) • ((c : 𝓞 E) • y) ∈ M
  exact M.smul_mem _ (M.smul_mem _ hy)

end Gen

theorem thDistC_class {X : Fields} (A : Amb X) {a b : ℕ} (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB) (c : ℕ)
    (x x' : HomE X.E a b) (h : x - x' ∈ mulLat c (homAt Sa N N')) :
    thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x = thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x' := by
  have hL : A.IsLift Sa N N' c x = A.IsLift Sa N N' c x' := by
    funext s
    unfold Amb.IsLift
    have : s - x ∈ mulLat c (homAt Sa N N') ↔ s - x' ∈ mulLat c (homAt Sa N N') := by
      rw [show s - x' = (s - x) + (x - x') by abel]
      exact (Submodule.add_mem_iff_left _ h).symm
    rw [this]
  have hW : A.liftW Sa N N' c x = A.liftW Sa N N' c x' := by unfold Amb.liftW; rw [hL]
  have hT : A.thInd Sa N N' c x = A.thInd Sa N N' c x' := by unfold Amb.thInd; rw [hW]
  have hJ : A.jetK Sa N N' c x = A.jetK Sa N N' c x' := by funext m; unfold Amb.jetK; rw [hT]
  have hD : x ∈ divLat D (homAt Sa N N') ↔ x' ∈ divLat D (homAt Sa N N') := by
    rw [show x = x' + (x - x') by abel]
    exact Submodule.add_mem_iff_left _ (mulLat_le_divLat c D _ h)
  unfold thDistC
  rw [hJ]
  exact @if_congr _ _ _ (_) (_) _ _ _ _ (and_congr_right fun _ => hD) rfl rfl

theorem ratTerm_of_ratStep : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → RatStep W Ch sel mu cst A u i (i + 1) → RatTerm W Ch sel mu cst A u i (i + 1) := by
  classical
  intro X Pr R W Ch sel S mu cst A u i _ hPr _ _ hR SG SG' d fr d' fr' Ξ₀ γ γ' hbox
  have hB : 0 < cBof sel mu cst u := by
    unfold cBof
    refine Nat.mul_pos (hPr.T_prime u).pos (pow_pos (Finset.prod_pos fun P _ => ?_) _)
    exact Nat.pos_of_ne_zero (by unfold Formalism.L2.Col.qOf; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)
  unfold term ker
  refine kerOf_move (stepT W Ch sel mu cst A u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i)))
    ((rhoVr X.emb (W.lamTrue u (i + 1))).comp (ufGL X.E (R.N (i + 1)))) γ γ' d.1.N fr (fun P => γ.1 * fr P) d'.1.N fr' (fun P => γ'.1 * fr' P)
    (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
    (fun x => phiT X.K (d.1.act γ.1 1) (d'.1.act γ'.1 1) x * Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) ?_ ?_ ?_ ?_
  · intro x x' h
    exact thDistC_class A _ _ _ _ _ _ _ _ _ _ _ _ _ _ x x' h
  · intro x
    by_cases hx : x ∈ divLat (cAof sel mu cst * cBof sel mu cst u) (homAt (Sall sel mu u) d.1.N d'.1.N)
    · exact hR γ γ' d.1.N fr d'.1.N fr' _ x ⟨⟨d.2.lat, d.2.uni⟩, ⟨d'.2.lat, d'.2.uni⟩, hB, Dvd.intro_left _ rfl, hx⟩
    · have hx2 := mt (mem_divLat_equiv_iff _ _ _ (homConjEquiv_mem_homAt (Sall sel mu u) γ.1 γ'.1 d.1.N d'.1.N)
        (cAof sel mu cst * cBof sel mu cst u) x).1 hx
      unfold stepT thDistC
      rw [if_neg fun h => hx2 h.2, if_neg fun h => hx h.2, LinearMap.zero_comp, LinearMap.comp_zero]
  · rintro x _ ⟨y₀, hy₀, rfl⟩
    refine congrArg₂ (· * ·) ?_ ?_
    · refine GlobalTheory.TopInv.phiT_add _ _ d'.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
      have h1 : Pr.piT u ∈ P.1.asIdeal := by
        have h := P.2
        unfold Primes.vT divs at h
        split_ifs at h with hf
        · simpa using h
        · simp at h
      rw [cBof, Nat.cast_mul, ← hPr.piT_norm]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
    · exact hbox.2 x _ ⟨y₀, fun P hP => hy₀ P (Finset.mem_union_right _ hP), rfl⟩
  · intro x
    refine congrArg₂ (· * ·) (phiT_move d.1 d'.1 γ.1 γ'.1 1 1 x) (congrArg Ξ₀ ?_)
    ext y l
    simp

end GlobalTheory.KerRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadPrimeNormPrimeNeLevelPrime
noncomputable section

namespace GlobalTheory.LvT.Built.IsTerm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
open GlobalTheory.ColPeriod GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

section Generic

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] {a b : ℕ} {P : HeightOneSpectrum (𝓞 E)}


omit [StarRing E] in
theorem awayAt_of_fnModAt {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Φ : HomE E a b → K}
    (hq : (qOf P).Prime) (h : FnModAt P N N' Φ) (w : HeightOneSpectrum (𝓞 K)) {B : ℕ} (hB : 1 ≤ B) : AwayAt P w B N N' Φ := by
  refine ⟨fun x => valuation_le_one_of_mem_Zmu w hq (h.2.2 x), fun x z hz => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hB
  rw [pow_succ', mul_smul]
  refine h.2.1 x _ ?_
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hz _

theorem exists_place (K : Type) [Field K] [NumberField K] {T : ℕ} (hT : T.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K), (T : 𝓞 K) ∈ w.asIdeal := by
  have h1 : Ideal.span {(T : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have h2 := Formalism.L2.Col.Primes.natCast_dvd_intCast (E := K) (c := T) (n := 1) (by simpa using h.dvd)
    exact hT.one_lt.ne' (Nat.dvd_one.1 (by exact_mod_cast h2))
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h1
  have h3 : (T : 𝓞 K) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, h3⟩
  rw [h, Ideal.mem_bot] at h3
  exact hT.ne_zero (by exact_mod_cast h3)

end Generic

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem badPrimeNorm_prime_ne_levelPrime (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) (P : rowSG Pr sel mu) :
    (qOf P.1).Prime ∧ qOf P.1 ≠ Pr.T u := by
  have h := levelPrimes X Pr sel S mu hX hPr hsel P
  refine ⟨h.1.1, fun e => ?_⟩
  by_cases hP : P.1 ∈ Pr.vGs
  · obtain ⟨k, hk⟩ := exists_mem_vG hP
    exact hPr.T_ne_g u k (e.symm.trans (hPr.vG_norm k _ hk))
  · exact h.2 hP (e ▸ hS)

theorem localization_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) {n : ℕ}
    {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : SameOff (Pr.vT u) N N') (P : rowSG Pr sel mu) :
    localization₂ P.1.asIdeal N = localization₂ P.1.asIdeal N' := by
  have h1 := badPrimeNorm_prime_ne_levelPrime hX hPr hsel hS P
  have h2 : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal :=
    natCast_notMem_of_ne (hPr.T_prime u) h1.1 h1.2.symm P.1 (Ideal.absNorm_mem _)
  refine h P.1 fun Q hQ => ?_
  have h3 := T_mem_of_piT_mem hPr u (GlobalTheory.ColPeriod.mem_divs hQ)
  refine ⟨fun e => h2 (e ▸ h3), fun e => h2 ?_⟩
  rw [e, mem_conjP, map_natCast]
  exact h3

theorem frsF_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) {j : ℕ} {p q : PtAt R sel mu cst u j}
    (h : SameOffPt sel mu cst u p q) : frsF sel mu q.1.1 = frsF sel mu p.1.1 := by
  funext P
  unfold frsF
  split_ifs with hP
  · have e : q.1.1.deco.1.at P.1 = p.1.1.deco.1.at P.1 := (localization_eq hX hPr hsel hS h.1 P).symm
    unfold Deco.liftFr
    simp only [e, h.2.1]
  · rw [h.2.2.1]

theorem awayAt_locTop (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) (hL : L.Ok Ch sel mu cst G m2)
    (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) {j : ℕ} (hj : j = R.m)
    (p : ChPt (R := R) sel mu u (m2 + 1)) {Y : Set (Sp X.E (R.N (m2 + 1)))} (hY : Y ∈ ybSet sel mu cst p.deco.1.N) :
    AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E (R.N j)) fun x =>
      TopStep.locTop Ch sel mu cst m2 P (castSp X.E (congrArg R.N hj) ∘ₗ x) ((frsF sel mu p P).symm (repY Y)) := by
  subst hj
  have hc := hL.cst_ok
  have hm := hL.hm
  have hq := badPrimeNorm_prime_ne_levelPrime hX hPr hsel hS P
  have key : ∀ v : Sp X.E (R.N R.m), v ∈ stdAt X.E _ P.1 ↔
      prXp X.E R v ∈ stdAt X.E (R.N R.m - 1) P.1 ∧ IntAt P.1 (atNL X.E (R.N R.m) (R.N R.m - 1) v) := fun v => by
    rw [GlobalTheory.LastSteps.atNL_last]
    exact TopStep.mem_stdAt_succ (N_m_succ R)
  change AwayAt P.1 w cst.B _ _ fun x => TopStep.locTop Ch sel mu cst m2 P x ((frsF sel mu p P).symm (repY Y))
  by_cases hP : P.1 ∈ Pr.vGs
  · have hy : (qOf P.1 : X.E) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
      rw [← map_smul, GlobalTheory.LastSteps.frsF_symm_mem sel mu p P hP]
      exact GlobalTheory.LastSteps.q_smul_repY sel mu cst hY P hP
    refine awayAt_of_fnModAt hq.1 ?_ w hc.B_pos
    refine (GlobalTheory.LastSteps.fnModAt_iff _ _ _).2 ((GlobalTheory.LastSteps.good_PhiTop Ch mu hm cst.sharp hP).mul
      (GlobalTheory.LastSteps.good_ftY sel mu cst hc P hP hy)
      (fun x => prXp X.E R ∘ₗ x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))
      (fun x => atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ x) (fun x z => ?_) (fun x z => ?_) fun w => ?_)
    · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
    · rw [LinearMap.comp_add, LinearMap.comp_smul]
    · rw [← LinearMap.comp_assoc, GlobalTheory.LastSteps.comp_funLeft_mem (GlobalTheory.LastSteps.cOf_top hm)]
      exact ⟨fun h => ⟨fun y hy => ((key _).1 (h y hy)).1, fun y hy => ((key _).1 (h y hy)).2⟩,
        fun h y hy => (key _).2 ⟨h.1 y hy, h.2 y hy⟩⟩
  · have hD := hL.depthQ P hP
    have hqw : ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal := natCast_notMem_of_ne hq.1 (hPr.T_prime u) hq.2 w hw
    have hy : ((qOf P.1 : X.E) ^ cst.M) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
      rw [← map_smul, ← TopTwist.frsF_mem' sel mu p P hP, LinearEquiv.apply_symm_apply]
      exact TopTwist.pow_smul_repY sel mu cst hY P hP
    refine ⟨fun x => ?_, fun x z hz => ?_⟩
    · unfold TopStep.locTop PhiTop
      rw [if_neg hP, map_mul]
      exact mul_le_one' (TopTwist.valuation_PhiQ w _ _ _ _ _ _ _ _ _) (TopTwist.valuation_ftY sel mu cst hc P hP hD w hqw hy _)
    · have hz' := fun y hy => (key _).1 (hz P.1 (Finset.mem_singleton_self _) y hy)
      have h1 : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
        unfold Ranks.r Ranks.N cOf
        rw [hm, mul_add (m2 + 1)]
        omega
      have h4 : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.N R.m - 1 + 0 := by
        unfold Ranks.N cOf
        rw [hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1)]
        omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc.B_pos
      unfold TopStep.locTop PhiTop
      dsimp only
      rw [if_neg hP]
      congr 1
      · have e : prXp X.E R ∘ₗ (x + ((qOf P.1 : X.E) ^ cst.B) • z) ∘ₗ
              LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
            prXp X.E R ∘ₗ x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) +
            (qOf P.1 : X.E) • ((((qOf P.1 : X.E) ^ k) • (prXp X.E R ∘ₗ z)) ∘ₗ
              LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
          rw [hk, pow_succ', mul_smul]
          simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc]
        rw [e]
        refine TopTwist.PhiQ_add _ h1 (h1.trans h4) _ _ ?_
        rw [GlobalTheory.LastSteps.comp_funLeft_mem (GlobalTheory.LastSteps.cOf_top hm), GlobalTheory.LastSteps.lamY_zero]
        exact fun y hy => TopStep.smul_mem_locP (TopStep.intAt_pow (TopStep.intAt_nat _) _) (hz' y hy).1
      · rw [LinearMap.comp_add, LinearMap.comp_smul]
        exact TopTwist.ftY_add sel mu cst hc P hP hD hy _ _ fun y hy => (hz' y hy).2

def MuqUnit (cst : LocCst X (rowSG Pr sel mu)) (R : Ranks) (u : Pr.Word) : Prop :=
  ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
    ∀ j, j < R.m → w.valuation X.K (cst.muq (j + 1) P) = 1

theorem muqUnit_of_tied (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) {σ₀ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → Formalism.L2.Host.HChar X.E}
    {eta : Formalism.L2.Host.HChar X.E} (ht : Ch.Tied σ₀ e m0 eta) : MuqUnit cst R u := by
  intro P w hP hw j hj
  have hq := badPrimeNorm_prime_ne_levelPrime hX hPr hsel hS P
  have hn := (levelPrimes X Pr sel S mu hX hPr hsel P).2 hP
  have hg' : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
    natCast_notMem_of_ne (hPr.g_prime k) hq.1 (fun h => hn (h ▸ hg k)) P.1 (Ideal.absNorm_mem _)
  have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal :=
    natCast_notMem_of_ne (hPr.T_prime u) hq.1 hq.2.symm P.1 (Ideal.absNorm_mem _)
  have h1 : w.valuation X.K (Ch.muVal ⟨j, hj⟩ P.1 : X.K) = 1 :=
    heckeUnit X Pr R.m Ch σ₀ (e ⟨j, hj⟩) ⟨j, hj⟩ (m0 ⟨j, hj⟩) hX hPr (ht.mu0 _) (Pr.T u) w P.1 (hPr.T_prime u) hw hT
      (Formalism.L2.Host.unif P.1) _ (ht.muVal _ P.1 hg')
  rw [hL.muqQ j hj P hP, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
    (twistUnit X.F X.E X.K S mu P.1 w).2, h1]
  simp

theorem exists_local (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S) (hL : L.Ok Ch sel mu cst G m2)
    (hU : MuqUnit cst R u) {i : ℕ} (hi : i < R.m) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) :
    ∃ Φ : rowSG Pr sel mu → Sp X.E (R.N i) → Sp X.E (R.N (i + 1)) → HomE X.E (R.N i) (R.N (i + 1)) → X.K,
      ∀ (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)),
        (∀ x, xiAt Ch sel mu cst L u i b b' p p' x = phiT X.K p.1.1.deco.1 p'.1.1.deco.1 x *
          ∏ P, Φ P ((frsF sel mu p.1.1 P).symm (repY p.1.2)) ((frsF sel mu p'.1.1 P).symm (repY p'.1.2))
            (inFr (frsF sel mu p.1.1 P) (frsF sel mu p'.1.1 P) x)) ∧
        ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
          AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _)
            (Φ P ((frsF sel mu p.1.1 P).symm (repY p.1.2)) ((frsF sel mu p'.1.1 P).symm (repY p'.1.2))) := by
  have hm := hL.hm
  have hq := badPrimeNorm_prime_ne_levelPrime hX hPr hsel hS (mu := mu)
  have hlp := levelPrimes X Pr sel S mu hX hPr hsel
  have heq := fun (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    (hP : P.1 ∉ Pr.vGs) => EntQ.entryAtQ volumeAtQ X Pr R Ch sel S mu cst L G m2 hL P w hP (hlp P).1
      (natCast_notMem_of_ne (hq P).1 (hPr.T_prime u) (hq P).2 w hw) (hU P w hP hw)
  rcases lt_trichotomy (i + 2) R.m with h | h | h
  · refine ⟨fun P _ _ => XiAt Ch sel mu cst i P (L.h i (b.get (by omega)) P) (L.h (i + 1) (b'.get (by omega)) P),
      fun p p' => ⟨fun x => ?_, fun P w hw => ?_⟩⟩
    · rw [xiAt_entry Ch sel mu cst L h (b.some_get (by omega)).symm (b'.some_get (by omega)).symm]
      rfl
    · by_cases hP : P.1 ∈ Pr.vGs
      · exact awayAt_of_fnModAt (hq P).1 (entryAtG X Pr R Ch sel S mu cst L G m2 hL i (by omega) _ _ P hP (hlp P).1) w
          hL.cst_ok.B_pos
      · exact (heq P w hw hP).1 i (by omega) _ _
  · obtain rfl : i = m2 := by omega
    refine ⟨fun P _ y x => PsiAt Ch sel mu cst i P (L.h i (b.get (by omega)) P) x y, fun p p' => ⟨fun x => ?_, fun P w hw => ?_⟩⟩
    · rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm]
      rfl
    · by_cases hP : P.1 ∈ Pr.vGs
      · exact awayAt_of_fnModAt (hq P).1 ((GlobalTheory.LastSteps.fnModAt_iff _ _ _).2
          (GlobalTheory.LastSteps.good_PsiAt Ch sel mu cst hm P hP (hL.stabG i _ P hP) _)) w hL.cst_ok.B_pos
      · exact (heq P w hw hP).2 _ _
  · obtain rfl : i = m2 + 1 := by omega
    have h1 : m2 + 1 + 1 = R.m := by omega
    refine ⟨fun P y _ x => TopStep.locTop Ch sel mu cst m2 P (castSp X.E (congrArg R.N h1) ∘ₗ x) y,
      fun p p' => ⟨fun x => ?_, fun P w hw => ?_⟩⟩
    · rw [xiAt_last Ch sel mu cst L h1]
      rfl
    · exact awayAt_locTop hX hPr hsel hS hL P w hw h1 p.1.1 (p.mem_ybSet h1)

theorem kerIsTerm_of_muqUnit (W : Wts X Pr.Word R) (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) (hU : MuqUnit cst R u) {i : ℕ} (hi : i < R.m) (A : Formalism.L2.Ker.Amb X) :
    KerIsTerm W Ch sel mu cst L A u i := by
  classical
  intro b b' p p'
  obtain ⟨Φ, hΦ⟩ := exists_local hX hPr hsel hS hL hU hi b b'
  have hA := fun P w hw => awayAt_inFr (isFrames_frsF p.1.1 P) (isFrames_frsF p'.1.1 P) ((hΦ p p').2 P w hw)
  refine ⟨fun x => if x ∈ divLat (cAof sel mu cst) (homAt (rowSG Pr sel mu) p.1.1.deco.1.N p'.1.1.deco.1.N) then
      ∏ P, Φ P ((frsF sel mu p.1.1 P).symm (repY p.1.2)) ((frsF sel mu p'.1.1 P).symm (repY p'.1.2))
        (inFr (frsF sel mu p.1.1 P) (frsF sel mu p'.1.1 P) x) else 0,
    ⟨fun x hx => ?_, fun x y hy => ?_⟩, fun w hw x => ?_, isFrames_frsF p.1.1, isFrames_frsF p'.1.1, fun q q' hq hq' => ?_⟩
  · by_contra h
    exact hx (if_neg h)
  · obtain ⟨w, hw⟩ := exists_place X.K (hPr.T_prime u)
    have hy' : y ∈ divLat (cAof sel mu cst) (homAt (rowSG Pr sel mu) p.1.1.deco.1.N p'.1.1.deco.1.N) := by
      obtain ⟨z, hz, rfl⟩ := hy
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hz)
    refine if_congr (Submodule.add_mem_iff_left _ hy') (Finset.prod_congr rfl fun P _ => ?_) rfl
    have hdv : qOf P.1 ^ cst.B ∣ cBof sel mu cst u :=
      Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) _
    obtain ⟨z, hz, rfl⟩ := exists_of_mem_mulLat hdv hy P.2
    rw [Nat.cast_pow]
    exact (hA P w hw).2 x z hz
  · dsimp only
    split_ifs
    · rw [map_prod]
      exact Finset.prod_le_one' fun P _ => (hA P w hw).1 x
    · simp
  · unfold kAt GlobalTheory.KerT.term GlobalTheory.KerT.ker kerOf latSum
    rw [frsF_eq hX hPr hsel hS hq, frsF_eq hX hPr hsel hS hq']
    refine finsum_congr fun z => ?_
    generalize Function.surjInv _ z = x
    obtain ⟨x, hx⟩ := x
    have hx' : x ∈ divLat (cAof sel mu cst) (homAt (rowSG Pr sel mu) p.1.1.deco.1.N p'.1.1.deco.1.N) := by
      intro P hP y hy
      rw [localization_eq hX hPr hsel hS hq.1 ⟨P, hP⟩] at hy
      rw [localization_eq hX hPr hsel hS hq'.1 ⟨P, hP⟩]
      exact hx P (Finset.mem_union_right _ hP) y hy
    dsimp only
    rw [if_pos hx', (hΦ q q').1, frsF_eq hX hPr hsel hS hq, frsF_eq hX hPr hsel hS hq', ← hq.2.2.2, ← hq'.2.2.2]

end Chain

theorem kerIsTerm : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → i < R.m → Ch.Ok → (∀ k, Pr.g k ∈ S) → (∃ (σ₀ : X.K →+* ℂ) (e : Fin R.m → X.Tau → ℚ) (m0 : Fin R.m → Formalism.L2.Host.HChar X.E) (eta : Formalism.L2.Host.HChar X.E), Ch.Tied σ₀ e m0 eta) → ∀ A : Formalism.L2.Ker.Amb X, KerIsTerm W Ch sel mu cst L A u i := by
  rintro X Pr R W Ch sel S mu cst L G m2 u i hX hPr hsel hS hL hi - hg ⟨σ₀, e, m0, eta, ht⟩ A
  exact kerIsTerm_of_muqUnit W hX hPr hsel hS hL (muqUnit_of_tied hX hPr hsel hS hg hL ht) hi A

end GlobalTheory.LvT.Built.IsTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SameOfAbove
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.UpLaw

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β]
  {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q} {pref : DecoF X.E n ST SG Q → Prop} {T : ℕ} {P : ST}
  (hP : MoveHyp ST SG P) (hT : (T : 𝓞 X.E) ∈ P.1.asIdeal ∧ (T : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
  (hQ : ∀ w : Q, w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1) (hy : y.Off P.1)

include hP hT hQ hy

theorem above_iff (b : β) (p q : PtY ST SG Q y) : Above (tdatY ST T y β Λ Θ pref) b P p q ↔
    p.1.1.deco.1.IsUp P (T : 𝓞 X.E) q.1.1.deco.1 ∧ q.1.1.1.2 = p.1.1.1.2 ∧ q.1.2 = p.1.2 := by
  constructor
  · rintro ⟨x, hx, hf, rfl⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨⟨x, hx, hf, h.1⟩, h.2⟩
  · rintro ⟨⟨x, hx, hf, e⟩, h2, h3⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨x, hx, hf, PtY.ext' (Subtype.ext (e.trans h.1.symm)) (h2.trans h.2.1.symm) (h3.trans h.2.2.symm)⟩

theorem bijOn_up (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P p q} {d | p.1.1.deco.1.IsUp P (T : 𝓞 X.E) d.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b p q).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b p q).1 hq).2
    have h' := ((above_iff hP hT hQ hy b p q').1 hq').2
    exact PtY.ext' e (h.1.trans h'.1.symm) (h.2.trans h'.2.symm)
  · obtain ⟨x, hx, hf, e⟩ := hd
    exact ⟨_, ⟨x, hx, hf, rfl⟩, Subtype.ext ((mv_up T p P hP hT hQ hy hx hf).1.trans e.symm)⟩

theorem bijOn_dn (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P q p} {d | d.1.IsUp P (T : 𝓞 X.E) p.1.1.deco.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b q p).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b q p).1 hq).2
    have h' := ((above_iff hP hT hQ hy b q' p).1 hq').2
    exact PtY.ext' e (h.1.symm.trans h'.1) (h.2.symm.trans h'.2)
  · have hs := fun w h1 h2 => (Deco.IsUp.sameAt d.2 hP hd (Q := w) h1 h2).localization_eq.symm
    have h := p.mv_spec d (fun w => hs w.1 (hQ w).1 (hQ w).2) (hy _ _ hs)
    refine ⟨p.mv d, (above_iff hP hT hQ hy b _ p).2 ⟨?_, h.2.1.symm, h.2.2.symm⟩, h.1⟩
    rw [h.1]
    exact hd

theorem same_of_above (b : β) {p q : PtY ST SG Q y} (h : Above (tdatY ST T y β Λ Θ pref) b P p q) :
    SameOff ST p.1.1.deco.1.N q.1.1.deco.1.N ∧ p.1.1.deco.1.be = q.1.1.deco.1.be ∧ p.1.1.fr = q.1.1.fr ∧ p.1.2 = q.1.2 := by
  obtain ⟨h1, h2, h3⟩ := (above_iff hP hT hQ hy b p q).1 h
  exact ⟨fun w hw => (h1.sameAt p.1.1.deco.2 hP (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm, h1.be_eq.symm,
    funext fun w => (congrFun h2 w).symm, h3.symm⟩

end Gen

theorem kAt_uk : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → GlobalTheory.KerT.UKTerm W Ch sel mu cst A u i (i + 1) → ∀ b b' (d : (stepAt sel mu cst L Tp u i).D b) (d' : (stepAt sel mu cst L Tp u (i + 1)).D b') (P : Pr.vT u) F, (∑ᶠ d₁ ∈ {d₁ | Above (tdatAt sel mu cst L Tp u (i + 1)) b' P d' d₁}, kAt W Ch sel mu cst L A u i b b' d d₁ F) = ((Pr.T u : X.K) ^ ((R.t + 1) / 2)) • ∑ᶠ d₀ ∈ {d₀ | Above (tdatAt sel mu cst L Tp u i) b P d₀ d}, kAt W Ch sel mu cst L A u i b b' d₀ d' F := by
  intro X Pr R W Ch sel S mu cst L G m2 u i hX hPr hsel hS _ Tp A hK hU b b' d d' P F
  obtain ⟨Ξ₀, hb, -, -, -, hk⟩ := hK b b' d d'
  have hP := moveHyp_of_ok hPr u P
  have hT := T_unif hX hPr u P
  have hQ0 := T_notMem_QE sel mu u hPr hsel hS
  have hQ : ∀ w : QE sel (mu : Chr X.F X.E X.K), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun w => ne_of_T_notMem hPr u P (hQ0 w.1 w.2)
  have hy := fun j => ysAt_off (R := R) sel mu cst hPr u hQ0 j P
  have refl : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p p :=
    fun p => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have key := hU d.1.1.deco (frsF sel mu d.1.1) d'.1.1.deco (frsF sel mu d'.1.1) Ξ₀ P F hP hP hb
  refine (finsum_mem_eq_of_bijOn _ (bijOn_up hP hT hQ (hy (i + 1)) b' d') fun q hq => ?_).trans
    (key.trans (congrArg _ (finsum_mem_eq_of_bijOn _ (bijOn_dn hP hT hQ (hy i) b d) fun q hq => ?_).symm))
  · rw [hk d q (refl d) (same_of_above hP hT hQ (hy (i + 1)) b' hq)]
  · obtain ⟨h1, h2, h3, h4⟩ := same_of_above hP hT hQ (hy i) b hq
    rw [hk q d' ⟨fun w hw => (h1 w hw).symm, h2.symm, h3.symm, h4.symm⟩ (refl d')]

end GlobalTheory.LvT.Built.UpLaw
end
end
