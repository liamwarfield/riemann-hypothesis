module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenStringOfAgreement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldConditionOfStandardKernelCompari
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueKernelJetsMulDetCharactersMemCoefficientFiel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueKernelJetsMulDetCharactersMemCoefficientFiel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.LvT.Built.KMap

theorem rho_jet_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ), (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) → ∃ k : B.LL, B.embLL k = (I.rho u a i c.1 ((I.stp u a i).rep c) * I.rho' u a i c'.1 ((I.stp u a (i + 1)).rep c')) * jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) e := by
  classical
  intro B X I h hP l Z hJ u a i hi c c' e he
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth I h hP l Z a u i hi
  set p := (I.stp u a i).rep c
  set p' := (I.stp u a (i + 1)).rep c'
  have hN : IsSdLat p.1.1.deco.1.N := ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩
  have hN' : IsSdLat p'.1.1.deco.1.N := ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) :=
    pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB : 0 < cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u := GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) _ _ u i hX hPr
    h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1 p p'
  set N := p.1.1.deco.1.N
  set N' := p'.1.1.deco.1.N
  set cA := cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a)
  set cB := cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u
  set Ξ := xiAt (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 p p'
  have hNfull : Submodule.IsFullLattice B.fields.E N := by
    let := hN.1
    refine { span_eq_top := ?_ }
    let W := Submodule.span B.fields.E (N : Set (Sp B.fields.E (B.R.N i)))
    change W = ⊤
    by_contra hspan
    let e : Sp B.fields.E (B.R.N i) ≃ₗ⋆[B.fields.E] Sp B.fields.E (B.R.N i) := starLinearEquiv B.fields.E
    let g : Sp B.fields.E (B.R.N i) →ₗ[B.fields.E] Module.Dual B.fields.E W :=
      (LinearMap.domRestrict' W).comp ((hStd B.fields.E (B.R.N i)).comp e.toLinearMap)
    have hdim : Module.finrank B.fields.E (Module.Dual B.fields.E W) < Module.finrank B.fields.E (Sp B.fields.E (B.R.N i)) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hspan
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : B.fields.E) : a • e x ∈ N := by
      rw [← hN.2, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd B.fields.E (B.R.N i) (e x) y = 0 :=
        congrArg (fun f : Module.Dual B.fields.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let j : B.fields.E →ₗ[𝓞 B.fields.E] N :=
      ((LinearMap.toSpanSingleton B.fields.E _ (e x)).restrictScalars (𝓞 B.fields.E)).codRestrict N hsmul
    let : Module.Finite (𝓞 B.fields.E) N := Module.Finite.iff_fg.mpr hN.1.fg
    let : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.Finite.of_injective j fun a b hab =>
      smul_left_injective B.fields.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField B.fields.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
  have hth := GlobalTheory.latSum_thInd_eq_thC B.fields I.A _ _ (I.Sb a u) N N' cA cB (fun x => I.A.σ₀ (Ξ x))
    (indTieD_of_la I.A _ _ _ _ (Nat.mul_pos hA hB) hLa) hN hN' hA hB (volC_pos_of_laHyp I.A _ _ _ hLa hN hN')
    (GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ _ _ _ _ _ hNfull hN'.1 hA hB) (fun x hx => hbox.1 x ((map_ne_zero _).1 hx))
    (fun x y hy => congrArg I.A.σ₀ (hbox.2 x y hy))
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ (I.Sb a u) N N' cA cB hNfull hN'.1 hA hB
  let _ := @Fintype.ofFinite _ hfin
  rw [show I.th u a i c.1 c'.1 p p' = fun z => _ from funext fun z => (hth z).symm]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((Formalism.L2.Col.mulLat cB (homAt (I.Sb a u) N N')).comap (divLat cA (homAt (I.Sb a u) N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (I.A.thInd (I.Sb a u) N N' cB (r q)) := fun q =>
    indSmooth_of I.A _ _ (I.Sb a u) (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  rw [show I.J.cD = I.A.cD from rfl, jetC_sum _ _ _ hs]
  have hr := rhoIs I h a u hi c.1 p c'.1 p'
  rw [show I.rho u a i c.1 p * I.rho' u a i c'.1 p' = _ from hr]
  have hσ : (ColIn.A I).σ₀ = B.embLL := rfl
  rw [hσ]
  apply RingHom.mem_fieldRange.1
  rw [mul_assoc, Finset.mul_sum]
  refine Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) (Subfield.sum_mem _ fun q _ => ?_)
  obtain ⟨y, hy⟩ := hJ.exists_eq (a := a) (u := u) (N := N) (N' := N') (c := cB) (x := (r q).1) (e := e) hi
    ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩ he
  rw [mul_left_comm]
  refine Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) ?_
  exact ⟨y, hy⟩

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueKernelJetsMulDetCharactersMemCoefficientFielStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ), (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) → ∃ k : B.LL, B.embLL k = (I.rho u a i c.1 ((I.stp u a i).rep c) * I.rho' u a i c'.1 ((I.stp u a (i + 1)).rep c')) * jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) e := by
  first | exact @GlobalTheory.Mem.Col2.TC.rho_jet_mem | exact GlobalTheory.Mem.Col2.TC.rho_jet_mem | (intros; apply GlobalTheory.Mem.Col2.TC.rho_jet_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldConditionOfStandardKernelCompari
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv

private theorem nuT_cast_eq_nuW {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau) (r : Fin (B.R.N i)) :
    ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = (B.wts.nuW u (i + 1) τ).w r := by

  have hq : ((B.wts.nuW u (i + 1) τ).w r : ℚ) = Examples₂.wtN (B.hcW u τ) r.1 + wG B.R ((B.hcW u τ).e ⟨i, hi⟩) (i + 1) := by
    rw [Formalism.L2.Col.Wts.nuW_eq _ u hi τ r]
    rw [show B.wts.lamN u i τ = Examples₂.lamOf (B.hcW u τ) i from rfl, Formalism.L2.Col.lamOf_wtN _ hi.le r]

  have hrow : DV.nuRow (I.rec7 l Z) u (i + 1) τ r = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
    rw [GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2]
    have h := congrArg (fun x : ℚ => (x : ℝ)) hq.symm
    simp only [Rat.cast_intCast] at h
    exact h

  have hnn : 0 ≤ (B.wts.nuW u (i + 1) τ).w r := by
    have h1 := Formalism.L2.Ker.natW_cast (B.wts.nuW u (i + 1) τ) r
    have h2 := GlobalTheory.MoveCompare.nuW_detShift_nonneg B.wts u hi τ
    omega
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  show ((⌊DV.nuRow (I.rec7 l Z) u (i + 1) τ r⌋₊ : ℕ) : ℤ) = _
  rw [hrow, hn, Int.cast_natCast, Nat.floor_natCast]

private theorem monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau)
    (m : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ)
    (hm : degAt m τ = ∑ r, nuT (I.rec7 l Z) u i τ r) : (monoDeg m τ : ℤ) = nuDeg B u i τ := by
  have h3 : ((∑ r, nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = nuDeg B u i τ := by
    push_cast
    exact Finset.sum_congr rfl fun r _ => nuT_cast_eq_nuW I l Z u hi τ r
  exact (congrArg (Nat.cast : ℕ → ℤ) hm).trans h3


set_option maxHeartbeats 800000 in
theorem rk_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → t.RK := by
  intro B X I hok hpins l Z L hT Gi Gl K Y cX ex t hJ hS u μ hμ i hi c c' m hm
  rw [hS.O.dgen u μ, hS.O.Th u μ i c c']
  exact GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField I hok hpins l Z hJ u μ i hi c c' m fun τ => monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT I l Z u hi τ m (hm τ)


end GlobalTheory.Pdv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldConditionOfStandardKernelCompariStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientFieldCondition_of_standardKernelComparison : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → t.RK := by
  first | exact @GlobalTheory.Pdv.rk_of_std | exact GlobalTheory.Pdv.rk_of_std | (intros; apply GlobalTheory.Pdv.rk_of_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainStabilisersEqStandardReaderPointsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainStabilisersEqStandardBaseLevelPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelQuotientEqTwistedTop
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.SumRowType

variable {E : Type} [Field E]

theorem atN_sumE_last {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t : ℕ) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) n = if n = t then 1 else 0 := by
  rw [Loc.atN, dite_eq_left (Nat.lt_succ_self n)]
  have h := sumE_last (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)
  have e : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Br.iL (rfl : n + 1 = n + 1) := rfl
  rw [e, h, Units.val_one, one_mul]
  rfl

theorem atN_sumE_up {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t s : ℕ) (hs : s < n) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) s = Loc.atN (j (Loc.eN E n t)) s := by
  rw [Loc.atN, dite_eq_left (by omega), Loc.atN, dite_eq_left hs]
  have h := congrFun (prH_sumE (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)) ⟨s, hs⟩
  have e1 : prH E (rfl : n + 1 = n + 1) (Loc.eN E (n + 1) t) = Loc.eN E n t := by
    funext i
    rw [prH_apply]
    rfl
  rw [e1] at h
  rw [← h, prH_apply]
  rfl

end GlobalTheory.SumRowType

namespace GlobalTheory.SumRowType

open Matrix in
theorem det_sumE {E : Type} [Field E] {n : ℕ} (r : ℕ) (hr : r ≤ n) (j : Sp E n ≃ₗ[E] Sp E n) :
    (Matrix.of fun s t : Fin (n + 1 - r) =>
        Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1).toLinearMap (Loc.eN E (n + 1) (r + t.1))) (r + s.1)).det =
      (Matrix.of fun s t : Fin (n - r) => Loc.atN (j.toLinearMap (Loc.eN E n (r + t.1))) (r + s.1)).det := by
  obtain ⟨m, rfl⟩ : ∃ m, n = r + m := ⟨n - r, by omega⟩
  have hm : r + m + 1 - r = m + 1 := by omega
  have hm' : r + m - r = m := by omega
  set A := Matrix.of fun s t : Fin (r + m + 1 - r) =>
    Loc.atN ((sumE (rfl : r + m + 1 = r + m + 1) j 1).toLinearMap (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) with hA
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm).symm A]
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm').symm]
  rw [Matrix.det_succ_row _ (Fin.last m)]
  rw [Finset.sum_eq_single (Fin.last m)]
  · have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) (Fin.last m) = 1 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + m))) (r + m) = 1
      rw [atN_sumE_last, if_pos rfl]
    rw [e1, Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, one_mul]
    congr 1
    ext s t
    show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) =
      Loc.atN (j (Loc.eN E (r + m) (r + t.1))) (r + s.1)
    exact atN_sumE_up j _ _ (by have := s.2; omega)
  · intro b _ hb
    have hb' : b.1 < m := Fin.val_lt_last hb
    have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) b = 0 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + b.1))) (r + m) = 0
      rw [atN_sumE_last, if_neg (by omega)]
    rw [e1, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lamQB_sumE : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  intro E K _ _ _ _ P ξ N n hN r hr j
  subst hN
  unfold LocE.lamQB
  rw [det_sumE r hr j]

end GlobalTheory.SumRowType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEqStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTypeCharacter_blockSumOne_eq : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  first | exact @GlobalTheory.SumRowType.lamQB_sumE | exact GlobalTheory.SumRowType.lamQB_sumE | (intros; apply GlobalTheory.SumRowType.lamQB_sumE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceLeTwistedK1
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceLeTwistedK1
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.PrincipalCongruenceLevelK1

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_shift {m c : ℕ} (hm : m ≤ c) {a d : E}
    (ha : IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * a)) (hd : IntAt P d) :
    IntAt P (((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  have e : ((qOf P : E) ^ (m : ℤ))⁻¹ * (a + (qOf P : E) ^ c * d) =
      ((qOf P : E) ^ (m : ℤ))⁻¹ * a + (qOf P : E) ^ (c - m) * d := by
    rw [zpow_natCast]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  rw [e]
  exact ha.add ((intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) _).mul hd)

theorem prinCong_maps {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) {x : Sp E N} (hx : x ∈ LocE.sclLat P (qOf P) N e) :
    (k : Sp E N ≃ₗ[E] Sp E N) x ∈ LocE.sclLat P (qOf P) N e := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  rw [ciMem_sclLat] at hx ⊢
  have hxs : x ∈ stdAt E N P := by
    rw [ciMem_stdAt]
    intro l
    obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
    have h1 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) m).mul (hx l)
    rw [hm, zpow_natCast] at h1
    rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h1
  have hd := mem_stdAt.1 (hk x hxs)
  intro l
  obtain ⟨m, hm⟩ : ∃ m : ℕ, e l.1 = m := ⟨(e l.1).toNat, by have := he l.1; omega⟩
  have hmc : m ≤ c := by have := he l.1; omega
  have e1 : (k : Sp E N ≃ₗ[E] Sp E N) x l = x l + (qOf P : E) ^ c * ((((qOf P : E) ^ c)⁻¹ • (k.1 x - x)) l) := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul]
    show _ = x l + ((k : Sp E N ≃ₗ[E] Sp E N) x l - x l)
    ring
  rw [e1, hm]
  have hxl := hx l
  rw [hm] at hxl
  exact intAt_shift P hmc hxl (hd l)

theorem prinCong_stab {N c : ℕ} {e : ℕ → ℤ} (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) {k : GLint E N P}
    (hk : k ∈ prinCong N P c) : (k : Sp E N ≃ₗ[E] Sp E N) ∈ stabL E N (LocE.sclLat P (qOf P) N e) := by
  intro x
  refine ⟨fun h => ?_, prinCong_maps P he hk⟩
  have h1 := prinCong_maps P he ((prinCong N P c).inv_mem hk) h
  have e2 : ((k⁻¹ : GLint E N P) : Sp E N ≃ₗ[E] Sp E N) ((k : Sp E N ≃ₗ[E] Sp E N) x) = x :=
    LinearEquiv.symm_apply_apply _ x
  rwa [e2] at h1

theorem principal_congruence_le_level_k1_at {N : ℕ} (r c : ℕ) (hc : 0 < c) : prinCong N P c ≤ twK1H P N r c := by
  intro k hk
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero (P := P)
  refine ⟨⟨k.2, ?_⟩, prinCong_stab P (fun l => ?_) hk, prinCong_stab P (fun l => ?_) hk, fun w hw => ?_⟩
  · exact prinCong_stab P (N := N + 0) (fun l => by split_ifs <;> omega) hk
  · unfold kOneLastExponents; split_ifs <;> omega
  · unfold twistedLevelExponent; split_ifs <;> omega
  · have hws : w ∈ stdAt E N P := by
      have h0 := prinCong_maps P (e := fun _ => 0) (fun _ => by omega) ((prinCong N P c).one_mem) (x := w) ?_
      · rw [ciMem_sclLat] at h0; rw [ciMem_stdAt]; intro l; simpa using h0 l
      · rw [ciMem_sclLat] at hw ⊢
        intro l
        have h1 := hw l
        unfold twistedLevelExponent at h1
        split_ifs at h1 with hl
        · simpa using h1
        · have h2 := (intAt_pow (P := P) (intAt_nat (P := P) (qOf P)) c).mul h1
          rw [zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul] at h2
          simpa using h2
    have hd := mem_stdAt.1 (hk w hws)
    rw [ciMem_sclLat]
    intro l
    have := hd l
    simp only [Pi.smul_apply, smul_eq_mul, zpow_natCast] at this ⊢
    exact this

theorem principal_congruence_le_level_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ),
    0 < c → prinCong N P c ≤ twK1H P N r c :=
  by
  intro E _ _ _ P N r c hc
  exact principal_congruence_le_level_k1_at P r c hc

end GlobalTheory.PrincipalCongruenceLevelK1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceLeTwistedK1Statement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_congruence_le_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ), 0 < c → prinCong N P c ≤ twK1H P N r c := by
  first | exact @GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 | exact GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 | (intros; apply GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopStep

theorem ext_mem_twisted_k1_level : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)),
    ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b →
    ∀ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → extI hN P j ∈ twK1H P N r c := by
  intro E _ _ _ P hq N n hN r b c hn j h
  subst hN
  have hent : ∀ k : GLint E n P, redGL n P k ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b →
      ∀ a l : Fin n, a.1 < r → r ≤ l.1 → IntAt P (k.1 (Pi.single a 1) l / (qOf P : E)) := by
    intro k hk a l ha hl
    have h0 : redP P (k.1 (Pi.single a 1) l) = 0 := by
      have := twTQ_HQ_entry hk ha hl
      rwa [redGL_val] at this
    exact intAt_div_of_redP hq (glint_entry k l a) h0
  refine mem_kOne_of_block P (n := n + 1) (r := r) (c := c) (by omega) (extI rfl P j) (j.1 : Sp E n ≃ₗ[E] Sp E n) ?_ ?_ ?_
  · intro x l
    rw [extI_val]
    by_cases hl : l.1 < n
    · rw [dite_eq_left (show l.1 < n + 1 - 1 by omega)]
      have := congrFun (prH_sumE rfl j.1 1 x) ⟨l.1, hl⟩
      exact this
    · rw [dite_eq_right (show ¬ l.1 < n + 1 - 1 by omega)]
      have e : l = Br.iL (rfl : n + 1 = n + 1) := Fin.ext (by have := l.2; show l.1 = n; omega)
      subst e
      rw [sumE_last, Units.val_one, one_mul]
  · exact fun a l ha hl => hent j h a l ha hl
  · intro a l ha hl
    have := hent j⁻¹ (by rw [map_inv]; exact inv_mem h) a l ha hl
    exact this

end GlobalTheory.TopStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1Statement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_ext_mem_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)), ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → extI hN P j ∈ twK1H P N r c := by
  first | exact @GlobalTheory.TopStep.ext_mem_twisted_k1_level | exact GlobalTheory.TopStep.ext_mem_twisted_k1_level | (intros; apply GlobalTheory.TopStep.ext_mem_twisted_k1_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelQuotientEqTwistedTop
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopLevQ

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem lamQB_prinCong (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N : ℕ} (r c : ℕ) (hc : 0 < c)
    (k : GLint E N P) (hk : k ∈ prinCong N P c) : LocE.lamQB ξ r N k.1.toLinearMap = 1 := by
  have h1 := redGL_of_prinCong hc hk
  refine twLamQB_red_one P ξ le_rfl k.1 fun s t _ _ _ _ => ⟨glint_entry k s t, ?_⟩
  have h2 := congrArg (fun M : GL (Fin N) (𝓞 E ⧸ P.asIdeal) => (M : Matrix (Fin N) (Fin N) (𝓞 E ⧸ P.asIdeal)) s t) h1
  simp only [redGL_val, Units.val_one, Matrix.one_apply] at h2
  exact h2

theorem levI_ext {N : ℕ} {P : HeightOneSpectrum (𝓞 E)} {A B : LevI E K N P} (e : A.H = B.H)
    (e' : ∀ k (h1 : k ∈ A.H) (h2 : k ∈ B.H), A.lam ⟨k, h1⟩ = B.lam ⟨k, h2⟩) : A = B := by
  obtain ⟨H, lam⟩ := A
  obtain ⟨H', lam'⟩ := B
  obtain rfl : H = H' := e
  obtain rfl : lam = lam' := MonoidHom.ext fun a => e' a.1 a.2 a.2
  rfl

theorem level_congruence_eq_twisted_k1 (P : HeightOneSpectrum (𝓞 E)) (hu : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {N n : ℕ} (hN : N = n + 1) (r b c : ℕ) (hn : n = r + b) :
    levCong hN P c ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩ = kOneLevel P N r (c + 1) ξ := by
  set l : Lev (𝓞 E ⧸ P.asIdeal) K n := ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩
  have hH : (levCong hN P c l).H = twK1H P N r (c + 1) := by
    refine le_antisymm (sup_le ?_ (GlobalTheory.T.principal_congruence_le_twisted_k1 P r (c + 1) c.succ_pos)) fun g hg => ?_
    · rintro _ ⟨j, hj, rfl⟩
      exact GlobalTheory.T.block_ext_mem_twisted_k1 P hu hN r b (c + 1) hn j hj
    · obtain ⟨j, hj, hb⟩ := GlobalTheory.T.twisted_k1_block_decomposition P hN r b c hn g hg
      exact (mem_levCong hN c l g).2 ⟨j, hj, hb⟩
  refine levI_ext hH fun k h1 h2 => ?_
  obtain ⟨j, hj, hb⟩ := (mem_levCong hN c l k).1 h1
  rw [levCong_lam hN c l h1 hj hb]
  apply Units.ext
  have hjK : extI hN P j ∈ twK1H P N r (c + 1) := GlobalTheory.T.block_ext_mem_twisted_k1 P hu hN r b (c + 1) hn j hj
  have hbK : (extI hN P j)⁻¹ * k ∈ twK1H P N r (c + 1) := GlobalTheory.T.principal_congruence_le_twisted_k1 P r (c + 1) c.succ_pos hb
  have hk : (⟨k, h2⟩ : twK1H P N r (c + 1)) = ⟨_, hjK⟩ * ⟨_, hbK⟩ := Subtype.ext (mul_inv_cancel_left _ _).symm
  show _ = ((kOneCharacter P N r (c + 1) ξ).toHomUnits ⟨k, h2⟩ : K)
  rw [MonoidHom.coe_toHomUnits, hk, map_mul]
  show _ = LocE.lamQB ξ r N (extI hN P j).1.toLinearMap * LocE.lamQB ξ r N ((extI hN P j)⁻¹ * k).1.toLinearMap
  rw [lamQB_prinCong P ξ r (c + 1) c.succ_pos _ hb, mul_one, extI_val, GlobalTheory.T.rowTypeCharacter_blockSumOne_eq P ξ hN r (by omega) j.1,
    GlobalTheory.TopLaw.lamQB_eq_red ξ hn j hj]
  rfl

end Gen

section Top

theorem levQTop_eq_twTt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → levQTop R sel mu (4 * R.m) = twTt (R := R) sel mu R.m := by
  intro X Pr R _ sel S mu hX hPr hsel _ _
  funext Q
  have hu : ((qOf Q.1 : ℕ) : 𝓞 X.E) ∉ Q.1.asIdeal ^ 2 :=
    (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel ⟨Q.1, by classical exact Finset.mem_union_right _ Q.2⟩).1.2
  exact level_congruence_eq_twisted_k1 Q.1 hu _ (N_m_succ R) R.r (R.m * R.t) (4 * R.m) (rank_X'_eq R)

end Top
end GlobalTheory.TopLevQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelQuotientEqTwistedTopStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_quotient_eq_twisted_top : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → levQTop R sel mu (4 * R.m) = twTt (R := R) sel mu R.m := by
  first | exact @GlobalTheory.TopLevQ.levQTop_eq_twTt | exact GlobalTheory.TopLevQ.levQTop_eq_twTt | (intros; apply GlobalTheory.TopLevQ.levQTop_eq_twTt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvGLawOfFixedCol
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker MvPolynomial

namespace GlobalTheory.KerJ

theorem ufGL_val {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix' γ.1.toLinearMap := by
  simp [ufGL, toGLm]
  rfl

end GlobalTheory.KerJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeLevelLastStepSymmetricRowsEqTwistLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeLevelLastStepSymmetricRowsEqTwistLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory

theorem levGTop_rPsymF_eq_twLt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok → Ch.Ok →
    levGTop Ch (rPsymF Ch) = twLt Ch R.m := by
  intro X Pr R Ch _ _ _
  funext w
  rw [levGTop_PsymF]
  show _ = colLevSym Ch R.m w
  unfold colLevSym
  rw [if_neg (by have := R.two_le_m; omega), dite_eq_right (by omega), dite_eq_right (by omega)]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeLevelLastStepSymmetricRowsEqTwistLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimeLevel_lastStep_symmetricRows_eq_twistLevel : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok → Ch.Ok → levGTop Ch (rPsymF Ch) = twLt Ch R.m := by
  first | exact @GlobalTheory.levGTop_rPsymF_eq_twLt | exact GlobalTheory.levGTop_rPsymF_eq_twLt | (intros; apply GlobalTheory.levGTop_rPsymF_eq_twLt <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pdv

theorem stabStd_eq_stabSet {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun γ => (fun v => γ.1 v) '' ((I.stp u a i).rep c).1.2 = ((I.stp u a i).rep c).1.2) := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    have hs : _ = _ := s.2
    refine ⟨s.1, congrArg (fun p => p.1.1) hs, congrArg (fun p => p.1.2) hs, ?_⟩
    refine Prod.ext ?_ rfl
    exact GlobalTheory.KerJ.ufGL_val s.1.1
  · rintro ⟨b, hb, hq, rfl⟩
    refine ⟨⟨b, Subtype.ext (Prod.ext hb hq)⟩, ?_⟩
    refine Prod.ext ?_ rfl
    exact (GlobalTheory.KerJ.ufGL_val b.1).symm

theorem rep_coset_empty {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m)
    (c : (I.stp u a i).Cl) : ((I.stp u a i).rep c).1.2 = ∅ := by
  have key : ∀ y : Ys B.fields (B.R.N i), y = Ys.triv _ _ → ∀ s N, s ∈ y.ys N → s = ∅ := by
    rintro y rfl s N hs
    exact hs
  exact key _ (by unfold ysAt; exact if_neg hi) _ _ ((I.stp u a i).rep c).2

theorem stabStd_eq_stabSet_triv {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun _ => True) := by
  rw [stabStd_eq_stabSet, rep_coset_empty I u a i hi c]
  congr 1
  funext γ
  simp

theorem stab_pin : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → ∀ u a, GlobalTheory.KerJ.StabPin t u a (GlobalTheory.Pdv.stabStd I l Z u a) := by
  intro B X I hI hP l Z L hT Gi Gl K Y cX ex t hN hK hR u a
  change B.Word at u
  change I.ι at a
  obtain ⟨cc, cc_rec, cc_ok, δ', δ_ok, B', χ, χ_ok, idl, idl_ok, χ_rec, cD, X', seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S', word,
    T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf,
    kf_un, served⟩ := t
  obtain ⟨hX, hseam, hPr, hCh, hsel, hS, hword, htup, hcst, hidx, hm2, -, -, -, -⟩ := hK
  subst hX
  obtain rfl := eq_of_heq hseam
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hCh
  obtain rfl := eq_of_heq hsel
  subst hS
  obtain rfl := eq_of_heq hword
  obtain rfl := eq_of_heq htup
  obtain rfl := eq_of_heq hcst
  obtain rfl := eq_of_heq hidx
  subst hm2
  obtain ⟨r, hr, hrs⟩ := hR u a
  obtain rfl := eq_of_heq hr
  unfold GlobalTheory.KerJ.StabPin
  dsimp only
  have hm : B.R.m = B.R.m - 2 + 2 := (hI.idx_ok a).hm
  have h1 : B.R.m - 2 + 1 + 1 = B.R.m := by omega
  obtain ⟨hXo, hPro, -⟩ := base_fields_primes_ok B X
  have hG : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levG j (b.get h) := by
    intro j b h
    unfold levGAt
    rw [← Idx.some_get b h]
    rfl
  have hQ : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levQ j (b.get h) := by
    intro j b h
    unfold levQAt
    rw [← Idx.some_get b h]
    rfl
  have hGt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twLt I.Ch B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levGAt
    rw [hb]
    exact (topLev_levG_m _ _ _ _ _).trans (GlobalTheory.T.typePrimeLevel_lastStep_symmetricRows_eq_twistLevel B.fields (B.primes X) B.R I.Ch hXo hPro hI.ch_ok)
  have hQt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twTt (R := B.R) I.sel (I.tup a) B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levQAt
    rw [hb]
    refine (topLev_levQ_m _ _ _ _ _).trans ?_
    have hd : topDep B.R (I.cst a).M = 4 * B.R.m := by
      have := (hN a).2.1
      unfold topDep
      exact max_eq_left (by omega)
    rw [hd]
    exact GlobalTheory.T.level_quotient_eq_twisted_top B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) hXo hPro hI.sel_ok (fun i => hI.g_mem i)
      (fun v => hI.T_mem v)
  have hTop : ∀ j (hj : j = B.R.m) (c : ((I.rec7 l Z).chTw u a).cls j),
      stabStd I l Z u a j c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (twLt I.Ch j)
        (twTt (R := B.R) I.sel (I.tup a) j) ((I.stp u a j).rep c).1.1 (fun _ => True) := by
    intro j hj c
    subst hj
    rw [stabStd_eq_stabSet_triv I l Z u a _ (by omega) c, hGt, hQt]
  refine ⟨fun i _ c => ((I.stp u a i).rep c).1.1, fun i hi c => c.1.get (by omega),
    fun c => ((I.stp u a (B.R.m - 2 + 1)).rep c).1.2, fun c => ((I.stp u a (B.R.m - 2 + 1 + 1)).rep c).1.1,
    fun i _ c => hrs.1 i c, fun c => PtAt.mem_ybSet _ h1, ?_, ?_, ⟨fun c' => hrs.1 _ c', ?_⟩, ?_, ?_, fun c => hTop _ h1 c⟩
  · intro i hi c c' x
    rw [hrs.2 i (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 _ _ x) = _
    rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm
      (Idx.some_get c'.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) c.1 c'.1 _ _ x) = _
    rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2 + 1) c.1 c'.1 _ _ x) = _
    rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) h1,
      GlobalTheory.T.lastColumnStepDatum_eq_twistTopDatum B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) u (B.R.m - 2) h1]
    rfl
  · intro i _ hi c
    rw [stabStd_eq_stabSet_triv I l Z u a i (by omega) c, hG i c.1 (by omega), hQ i c.1 (by omega)]
    rfl
  · intro b c
    obtain ⟨b0, hb0⟩ := (hI.idx_ok a).last_uniq
    have hcb : c.1.get (by omega) = b := (hb0 _).trans (hb0 b).symm
    rw [stabStd_eq_stabSet, hG _ c.1 (by omega), hQ _ c.1 (by omega), hcb]
    rfl

end GlobalTheory.Pdv

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChain_stabilizers_eq_standardBaseLevel_points : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → ∀ u a, GlobalTheory.KerJ.StabPin t u a (GlobalTheory.Pdv.stabStd I l Z u a) := by
  first | exact @GlobalTheory.Pdv.stab_pin | exact GlobalTheory.Pdv.stab_pin | (intros; apply GlobalTheory.Pdv.stab_pin <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardKernelDataWithStandardReadersStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardKernelDataWithStandardBaseLevels
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Pdv.stdKer_stdRd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardKernelData_with_standardBaseLevels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned := by
  first | exact @GlobalTheory.Pdv.stdKer_stdRd | exact GlobalTheory.Pdv.stdKer_stdRd | (intros; apply GlobalTheory.Pdv.stdKer_stdRd <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnSidePropertiesTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnSidePropertiesTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.Pdv

theorem colSide_of_choices {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hN : GlobalTheory.Pdv.ColNorm I)
    (hX_eq : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hS : t.S = I.S) (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst)
    (hidx : HEq t.idx I.idx) (hm2 : t.m2 = B.R.m - 2) (hglob : HEq t.glob I.glob) : GlobalTheory.KerJ.ColSide t := by
  have hb := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have kCst : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
      (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S') (cst' : ∀ μ, LocCst X' (rowSG Pr' sel' (tup' μ))),
      X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq cst' I.cst →
      ∀ μ, (cst' μ).sharp = true ∧ (I.rec7 l Z).R.m ≤ (cst' μ).A ∧ 2 * (cst' μ).M ≤ twTopDepth (I.rec7 l Z).R := by
    rintro X' Pr' sel' S' tup' cst' rfl h1 h2 rfl h3 h4
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    obtain rfl := eq_of_heq h3
    obtain rfl := eq_of_heq h4
    intro μ
    have h5 := (hN μ)
    refine ⟨hI.sharp μ, h5.1, ?_⟩
    show 2 * (I.cst μ).M ≤ 4 * B.R.m + 1
    omega
  refine ⟨?fields, ?sel, ?bad, ?chOk, ?chars, ?sharp, ?deep, ?repOne⟩
  case fields => exact hX_eq ▸ hb.1
  case sel =>
    have key : ∀ (X' : Fields) (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)),
        X' = B.fields → HEq sel' I.sel → IsSel X' sel' := by
      rintro X' sel' rfl h
      obtain rfl := eq_of_heq h
      exact hI.sel_ok
    exact key _ _ hX_eq hsel
  case bad =>
    have key : ∀ (X' : Fields) (Pr' : Primes X'), X' = B.fields → HEq Pr' (B.primes X) → ∀ v, Pr'.T v ∈ I.S := by
      rintro X' Pr' rfl h
      obtain rfl := eq_of_heq h
      exact hI.T_mem
    rw [hS]
    refine ⟨fun i => ?_, key _ _ hX_eq hPr, fun _ hl => hI.small_mem hl, hI.two_q_d_mem.2.1⟩
    rw [t.g_rec]
    exact hI.g_mem i
  case chOk =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → Ch'.Ok := by
      rintro X' Pr' Ch' rfl h1 h2
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      exact hI.ch_ok
    exact key _ _ _ hX_eq hPr hCh
  case chars =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m) (glob' : ChGlob X' (I.rec7 l Z).R.m)
        (seam' : Seam (I.rec7 l Z) X'), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → HEq glob' I.glob → HEq seam' (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) →
        ∃ eta, Ch'.Tied glob'.σ₀ (fun j τ => ((I.rec7 l Z).hc (seam'.iT τ)).e j) glob'.mu0 eta := by
      rintro X' Pr' Ch' glob' seam' rfl h1 h2 h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      exact ⟨I.C.eta, hI.ch_tied⟩
    exact key _ _ _ _ _ hX_eq hPr hCh hglob hseam
  case sharp => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).1
  case deep => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).2
  case repOne =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
        (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S')
        (idx' : ∀ μ, ChIdx X' Pr' (I.rec7 l Z).R (QE sel' (tup' μ : Chr X'.F X'.E X'.K))),
        X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq idx' I.idx →
        ∀ μ j, j ≤ B.R.m - 2 + 1 → ∀ (b : (idx' μ).β j) (P : rowSG Pr' sel' (tup' μ)), P.1 ∈ Pr'.vGs → (idx' μ).h j b P = 1 := by
      rintro X' Pr' sel' S' tup' idx' rfl h1 h2 rfl h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      intro μ
      exact (hN μ).2.2
    rw [hm2]
    exact key _ _ _ _ _ _ hX_eq hPr hsel hS htup hidx

theorem colSide_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.KerJ.ColSide t := by
  intro B X I hI _ l Z L hT Gi Gl K Y cX ex t hN hS
  exact colSide_of_choices I hI l Z t hN hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.tup hS.cst hS.idx hS.m2 hS.glob

end GlobalTheory.Pdv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnSidePropertiesTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnSide_properties_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.KerJ.ColSide t := by
  first | exact @GlobalTheory.Pdv.colSide_of_std | exact GlobalTheory.Pdv.colSide_of_std | (intros; apply GlobalTheory.Pdv.colSide_of_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConditionsAtStandardKernelComparisonTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.duty_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → GlobalTheory.Pdv.Duty t := by
  intro B X I hOk hP l Z l0 L hT Gi Gl K Y cX ex t hN hJ htw hS hE
  obtain ⟨t', hS', hR', -⟩ := GlobalTheory.T.standardKernelData_with_standardBaseLevels I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  refine ⟨GlobalTheory.T.columnSide_properties_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t hN hS, hE, GlobalTheory.T.coefficientFieldCondition_of_standardKernelComparison I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS,
    ⟨t', GlobalTheory.T.columnSide_properties_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS', ?_⟩⟩
  intro u μ _
  refine ⟨GlobalTheory.Pdv.stabStd I l Z u μ, ?_, GlobalTheory.T.trueChain_stabilizers_eq_standardBaseLevel_points I hOk hP l Z L hT Gi Gl K Y cX ex t' hN hS' hR' u μ⟩
  rw [htw]
  exact GlobalTheory.T.trueChain_complexForms_stabiliser_law I hOk hP l Z l0 Y.Qp t'.O hS'.O u μ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConditionsAtStandardKernelComparisonTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conditions_at_standardKernelComparison_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → GlobalTheory.Pdv.Duty t := by
  first | exact @GlobalTheory.Pdv.duty_of_std | exact GlobalTheory.Pdv.duty_of_std | (intros; apply GlobalTheory.Pdv.duty_of_std <;> assumption)
end
