module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrime
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLatticeAtClassIffTwistedPolynomial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexValueDetShiftMulRatSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexValueDetShiftMulRatSpan
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerValRat

theorem lamTG_add_sSharp {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (lamTG M i τ).w r + (D.chTw u μ).sSharp i τ = (nuT D u i τ r : ℤ) := by
  obtain ⟨a, ha⟩ := D.R.t_odd
  have hc : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) = (i : ℝ) * ((a : ℝ) + 1) := by
    rw [ha, show i * (2 * a + 1 + 1) = 2 * (i * (a + 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast; ring
  have ht : (D.R.t : ℝ) = 2 * a + 1 := by rw [ha]; push_cast; ring
  have h1 := congrArg (Rat.cast : ℚ → ℝ) (M.lam_eq i hi.le τ r)
  have h2 := congrArg (Rat.cast : ℚ → ℝ) ((D.chTw u μ).sSharp_eq i hi τ)
  have h3 := GlobalTheory.PdvKm.nuT_real u i hi τ r
  have he := D.hcW_e u τ
  suffices key : (((lamTG M i τ).w r : ℤ) : ℝ) + (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((nuT D u i τ r : ℕ) : ℝ) by
    exact_mod_cast key
  rw [h3]
  have e0 : (lamTG M i τ).w r = (M.lam i τ).w r - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) := rfl
  have hl : (((lamTG M i τ).w r : ℤ) : ℝ) = ((((M.lam i τ).w r : ℤ) : ℚ) : ℝ) - (i : ℝ) * ((a : ℝ) + 1) := by
    rw [e0, Int.cast_sub, Int.cast_natCast, hc, Rat.cast_intCast]
  have hs : (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((((D.chTw u μ).sSharp i τ : ℤ) : ℚ) : ℝ) := by rw [Rat.cast_intCast]
  rw [hl, hs, h1, h2]
  have hw : DV.wSz D (i + 1) τ = (((D.hcW u τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dite_eq_left ⟨by omega, by omega⟩, he]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar sExp' Ranks.N
  by_cases hk : r.1 < D.R.k
  · rw [dite_eq_left hk, dite_eq_left hk]
    unfold hcToWeightQ rhoVec
    push_cast
    rw [ht]
    ring
  · rw [dite_eq_right hk, dite_eq_right hk]
    have hr := r.2
    unfold Ranks.N at hr
    have hb : (r.1 - D.R.k) / (D.R.t + 1) < i := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact Nat.sub_lt_left_of_lt_add (by omega) hr
    have hbm : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by omega
    rw [dite_eq_left hbm]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hr' : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + ((D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1)) := by omega
      conv_lhs => rw [this]
      push_cast; ring
    unfold wG
    push_cast
    rw [hr', ht]
    ring

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem detShift_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    (lamTG M i τ).detShift = (nuT D u i τ (lastI D i) : ℤ) - (D.chTw u μ).sSharp i τ := by
  have h := lamTG_add_sSharp M μ i hi τ (lastI D i)
  unfold DomWeight.detShift
  rw [dite_eq_left (N_pos D i)]
  show (lamTG M i τ).w (lastI D i) = _
  omega

open GlobalTheory.PdvKm in
theorem natW_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (M.lam i τ).natW r = nuT D u i τ r - nuT D u i τ (lastI D i) := by
  have h0 : (M.lam i τ).natW r = (lamTG M i τ).natW r := by
    show _ = (Formalism.L2.Forms.shW (M.lam i τ) _).natW r
    rw [Formalism.L2.Forms.natW_shW]
  rw [h0]
  have h1 := lamTG_add_sSharp M D.what₂.mu0 i hi τ r
  have h2 := detShift_lamTG M D.what₂.mu0 i hi τ
  have hle : nuT D u i τ (lastI D i) ≤ nuT D u i τ r :=
    antitone_kernelChain_nuT D u i τ hi (show r ≤ lastI D i by rw [Fin.le_def]; simp only [lastI]; omega)
  unfold DomWeight.natW
  rw [h2]
  omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem evC_ratSpan_gen {D : D7} (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {A : ColumnsAtT D.R (D.chTw u μ)} {P : PeriodMap D.R (D.chTw u μ)}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) (D.chTw u μ) A P)
    (i : ℕ) (hi : i < D.R.m) (eY : (D.chTw u μ).Y i ≃ Fr D i hi.le)
    (hfrm : ∀ y, (O u μ).frm i y = (eY y).1) (v : ValQ O u μ i) :
    ∃ Q ∈ Formalism.L2.Forms.RatSpan D (M.lam i), ∀ z, evC O u μ i v z =
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) := by
  have hne : ∀ (z : (D.chTw u μ).Y i) τ, ((eY z).1 τ).det ≠ 0 := fun z τ => by
    rw [← hfrm z, ← (O u μ).frm_de i hi.le z τ]; exact (D.chTw u μ).de_ne i z τ
  have hev : ∀ z, evC O u μ i v z = (∏ τ, (((eY z).1 τ).det) ^ (-(twB D u μ i τ))) *
      MvPolynomial.eval₂ D.what₂.embLL (fun k => (eY z).1 k.1 k.2.1 k.2.2)
        (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) := by
    intro z
    rw [evC_sec]
    show (∏ τ, ((D.chTw u μ).de i z τ) ^ (-(twB D u μ i τ))) *
      GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i z) = _
    simp only [(O u μ).frm_de i hi.le z, hfrm z, evFr_map]
  have hfn : ∀ (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) z,
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) =
        (∏ τ, ((eY z).1 τ).det ^ (lamTG M i τ).detShift) * MvPolynomial.eval (fun x => (eY z).1 x.1 x.2.1 x.2.2) Q := by
    intro Q z
    show (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) τ * (eY z).1 τ).det ^ _) *
      MvPolynomial.eval (fun x => ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) x.1 * (eY z).1 x.1) x.2.1 x.2.2) Q = _
    simp only [Pi.one_apply, one_mul]
    rfl

  haveI hLL : Infinite D.what₂.LL := Infinite.of_injective (fun n : ℕ => (n : D.what₂.LL)) (fun a b h => by
    have := congrArg D.what₂.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hmem : (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) ∈ polV D u i := (secC O u μ i v).2
  rcases i with _ | j
  · have h0 : 0 < D.R.m := hi
    have hk : ∀ τ r, nuT D u 0 τ (lastI D 0) ≤ nuT D u 0 τ r := fun τ r =>
      antitone_kernelChain_nuT D u 0 τ h0 (show r ≤ lastI D 0 by rw [Fin.le_def]; simp only [lastI]; omega)
    obtain ⟨P0, hP0, hQe⟩ := frameWeightPolyDivByDet_proof D.what₂.LL D.what₂.Tau (D.R.N 0) (nuT D u 0) (fun τ => nuT D u 0 τ (lastI D 0)) hk _ hmem
    refine ⟨MvPolynomial.map D.what₂.embLL P0, GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam 0) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam 0 τ).natW r) = fun τ r => nuT D u 0 τ r - nuT D u 0 τ (lastI D 0) :=
        funext fun τ => funext fun r => natW_lamTG M 0 h0 τ r
      rw [e]; exact hP0
    · have hd : ∀ τ, MvPolynomial.eval₂ D.what₂.embLL (fun k : GL3Theta.FrV D (D.R.N 0) => (eY z).1 k.1 k.2.1 k.2.2)
          (frDet D.what₂.LL (D.R.N 0) τ) = ((eY z).1 τ).det := by
        intro τ
        rw [← MvPolynomial.eval_map, Formalism.L2.Ker.map_frDet, Formalism.L2.Ker.eval_frDet]
        rfl
      rw [hev, hfn, hQe, MvPolynomial.eval_map, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod]
      simp only [MvPolynomial.eval₂_pow, hd]
      have hs : ∀ τ, (lamTG M 0 τ).detShift = ((nuT D u 0 τ (lastI D 0) : ℕ) : ℤ) - twB D u μ 0 τ :=
        fun τ => detShift_lamTG M μ 0 h0 τ
      simp only [hs]
      rw [prod_zpow_split _ (hne z) _ (fun τ => nuT D u 0 τ (lastI D 0))]
      ring
  · have hj : j < D.R.m := by omega
    refine ⟨MvPolynomial.map D.what₂.embLL (secC O u μ (j + 1) v : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) D.what₂.LL),
      GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam (j + 1)) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam (j + 1) τ).natW r) = extNu (D.R.N (j + 1)) (nuT D u j) := by
        funext τ r
        rw [natW_lamTG M (j + 1) hi τ r, ← natW_succ (antitone_kernelChain_nuT D) u j hj τ r]
        have h1 := clause1 (antitone_kernelChain_nuT D) u (j + 1) hi τ r
        have h2 : nn D u (j + 1) τ = nuT D u (j + 1) τ (lastI D (j + 1)) := by unfold nn; rw [if_pos hi]
        omega
      rw [e]; exact hmem
    · rw [hev, hfn, MvPolynomial.eval_map]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      rw [detShift_lamTG M μ (j + 1) hi τ]
      have h1 := last_real u μ j hi τ
      show -((D.chTw u μ).sDiv j τ) = _
      have h2 : ((nuT D u (j + 1) τ (lastI D (j + 1)) : ℕ) : ℤ) = (D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ := by
        exact_mod_cast h1
      omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

theorem evC_ratSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ v : ValQ O u μ i, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, evC O u μ i v z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z) := by
  intro B X I hOk hPins l Z Y O hQ hS u μ i hi eY hId v
  exact evC_ratSpan_gen O u μ (I.fm l u μ) i hi eY (fun y => (hS.frm u μ i y).trans (hId y).symm) v

end GlobalTheory.KerValRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexValueDetShiftMulRatSpanStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexValue_det_shift_mul_ratSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ v : ValQ O u μ i, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, evC O u μ i v z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z) := by
  first | exact @GlobalTheory.KerValRat.evC_ratSpan | exact GlobalTheory.KerValRat.evC_ratSpan | (intros; apply GlobalTheory.KerValRat.evC_ratSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeLocalBasisIffUnimodularCompanion
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeLocalBasisIffUnimodularCompanion
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.DualOffLevel

theorem mem_divs_of {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact (hf.mem_toFinset.1 h)
  · simp at h

theorem isLocBasis_dual_iff_N : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (u : B.Word) (a : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u a w → ∀ (i : ℕ) (hi : i ≤ B.R.m) (c : (I.stp u a i).Cl) (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c))) Bm ↔ Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u a i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm := by
  intro B X I hOk hPins l Z Y u a w hw i hi c Bm
  classical
  have hpP : ((I.rec7 l Z).what₂.places.resChar w).Prime := (I.rec7 l Z).what₂.places.resChar_prime w
  have hTP : (B.T u).Prime := l.pr.T_prime u
  have hpT : ¬ (I.rec7 l Z).what₂.places.resChar w ∣ B.T u := fun h => hw.1 ((Nat.prime_dvd_prime_iff_eq hpP hTP).1 h)
  obtain ⟨hG, -, hc⟩ := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi
  have hL := (hc u a).1 c
  have hS : dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)
      (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) =
      (((I.stp u a i).rep c).1.1.deco.1.Lsh : Set (Sp B.fields.E (B.R.N i))) := by
    rw [hG, hL]
    exact GlobalTheory.Mem.Col2.ValTie.dualSet_std (E := B.fields.E) _ (fun _ => rfl) _
  rw [hS]
  set d := ((I.stp u a i).rep c).1.1.deco with hd
  have hTP' : ∀ P : (B.primes X).vT u, (((B.T u : ℕ) : 𝓞 B.fields.E)) ∈ (P : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    intro P
    have hpi := mem_divs_of P.2
    rw [← l.pr.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  have hLN : ∀ x ∈ d.1.Lsh, ((B.T u : ℕ) : B.fields.E) • x ∈ d.1.N := by
    intro x hx
    have := d.2.smul_Lsh_mem_N (a := ((B.T u : ℕ) : 𝓞 B.fields.E)) (fun P => by rw [map_natCast]; exact hTP' P) hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul B.fields.E] at this
  unfold Formalism.L2.Forms.IsLocBasis
  refine forall_congr' fun x => iff_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨s, hs, hx⟩
    refine ⟨B.T u * s, fun h => (hpP.dvd_mul.1 h).elim hpT hs, ?_⟩
    have h3 := hLN _ hx
    have e : ((B.T u * s : ℕ) : (I.rec7 l Z).host.E) • x = ((B.T u : ℕ) : (I.rec7 l Z).host.E) • ((s : (I.rec7 l Z).host.E) • x) := by
      rw [smul_smul, ← Nat.cast_mul]
    exact e ▸ h3
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, d.2.N_le_Lsh hx⟩

end GlobalTheory.DualOffLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeLocalBasisIffUnimodularCompanionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (u : B.Word) (a : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u a w → ∀ (i : ℕ) (hi : i ≤ B.R.m) (c : (I.stp u a i).Cl) (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c))) Bm ↔ Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u a i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm := by
  first | exact @GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N | exact GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N | (intros; apply GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueChainsKernelDatumSourceSideLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.KerLatS

theorem charts_read_step {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (him : i < B.R.m) :
    ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch)
      (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K := by
  classical
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact GlobalTheory.T.exists_charts_reading_step_zero I hOk hPins l Z u a
  · obtain ⟨Ch0, _, chOf0, K0, hK0, -⟩ := GlobalTheory.T.exists_memberStep_charts I hOk hPins l Z u i hi
    obtain ⟨Ch, _, chOf, K, -, hK, -⟩ := GlobalTheory.T.tupleChain_middleStage_charts_joined_member I hOk hPins l Z u a ((I.Q a).image fun P => P.under (𝓞 B.host.F)) i hi
      Ch0 chOf0 K0 h1 him (fun v => Finset.mem_image) hK0
    exact ⟨_, Ch, chOf, K, hK⟩

theorem kerEntHyp_latS : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls i → ((I.rec7 l Z).chTw u μ).Y i → ℂ, (∃ x ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat i).L, ((I.tw l l0 Z).fm u μ).emb i x = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi i ∧ ∀ c, ∃ v : ValQ O u μ i, evC O u μ i v = φ c ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt _hUnf _hJets u μ w hw i hi φ
  obtain ⟨bad, Ch, chOf, K, hK⟩ := charts_read_step I hOk hPins l Z u μ i hi.le hi
  have hY : I.IdY l Z u μ i hi.le (Equiv.refl _) := fun _ => rfl
  have V := GlobalTheory.T.hermitianChart_complex_rational_integral_forms I hOk hPins l Z u μ i hi.le bad Ch chOf K (Equiv.refl _) hK hY
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hrat := (V.rat ((I.fm l u μ).emb i x)).1 ⟨x, rfl⟩
    have hlat := (V.lat w trivial x).1 hx
    refine ⟨hrat.1, fun c => ?_⟩
    obtain ⟨Bm, hBm⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis ((I.rec7 l Z).what₂.places.resChar w) _ _
      ((I.stp u μ i).rep c).1.1.deco.2.lat.fg (by
        open Formalism.HermitianLatticesTheory Module in
        let L := ((I.stp u μ i).rep c).1.1.deco.1.N
        have hL := ((I.stp u μ i).rep c).1.1.deco.2.lat
        have hu : IsUnimodular (Formalism.L2.Col.hStd B.fields.E (B.R.N i)) L :=
          ((I.stp u μ i).rep c).1.1.deco.2.uni
        let W := Submodule.span B.fields.E (L : Set (Sp B.fields.E (B.R.N i)))
        change W = ⊤
        by_contra h
        let e : Sp B.fields.E (B.R.N i) ≃ₗ⋆[B.fields.E] Sp B.fields.E (B.R.N i) := starLinearEquiv B.fields.E
        let g : Sp B.fields.E (B.R.N i) →ₗ[B.fields.E] Module.Dual B.fields.E W :=
          (LinearMap.domRestrict' W).comp ((Formalism.L2.Col.hStd B.fields.E (B.R.N i)).comp e.toLinearMap)
        have hdim : finrank B.fields.E (Module.Dual B.fields.E W) <
            finrank B.fields.E (Sp B.fields.E (B.R.N i)) := by
          rw [Subspace.dual_finrank_eq]
          exact Submodule.finrank_lt h
        obtain ⟨x, hx, hx₀⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
        have hsmul (a : B.fields.E) : a • e x ∈ L := by
          rw [← hu, dualBasic_mem_dual]
          intro y hy
          apply hStd_mem_one_symm
          have hxy : Formalism.L2.Col.hStd B.fields.E (B.R.N i) (e x) y = 0 :=
            congrArg (fun f : Module.Dual B.fields.E W => f ⟨y, Submodule.subset_span hy⟩)
              (LinearMap.mem_ker.mp hx)
          simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
        let j : B.fields.E →ₗ[𝓞 B.fields.E] L :=
          ((LinearMap.toSpanSingleton B.fields.E _ (e x)).restrictScalars (𝓞 B.fields.E)).codRestrict L hsmul
        let : Module.Finite (𝓞 B.fields.E) L := Module.Finite.iff_fg.mpr hL.fg
        let : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.Finite.of_injective j fun a b hab =>
          smul_left_injective B.fields.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hab)
        exact RingOfIntegers.not_isField B.fields.E
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E)))
    have hBm' := (GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion I hOk hPins l Z Y u μ w hw i hi.le c Bm).2 hBm
    exact (GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat.2 c) Bm
      hBm).1 (hlat c Bm hBm')
  · rintro ⟨hFi, hc⟩
    have hrat : ∀ c, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, φ c z =
        fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P
          ((Equiv.refl _) z) := by
      intro c
      obtain ⟨v, hv, -⟩ := hc c
      rw [← hv]
      exact GlobalTheory.T.complexValue_det_shift_mul_ratSpan I hOk hPins l Z Y O hQp hStd u μ i hi (Equiv.refl _) hY v
    obtain ⟨x, hx⟩ := (V.rat φ).2 ⟨hFi, hrat⟩
    refine ⟨x, (V.lat w trivial x).2 fun c Bm hBm => ?_, hx⟩
    have hBm' := (GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion I hOk hPins l Z Y u μ w hw i hi.le c Bm).1 hBm
    have h1 := (GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat c) Bm
      hBm').2 (hc c)
    rw [hx]
    exact h1

end GlobalTheory.KerLatS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueChainsKernelDatumSourceSideLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChains_kernelDatum_sourceSideLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls i → ((I.rec7 l Z).chTw u μ).Y i → ℂ, (∃ x ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat i).L, ((I.tw l l0 Z).fm u μ).emb i x = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi i ∧ ∀ c, ∃ v : ValQ O u μ i, evC O u μ i v = φ c ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  first | exact @GlobalTheory.KerLatS.kerEntHyp_latS | exact GlobalTheory.KerLatS.kerEntHyp_latS | (intros; apply GlobalTheory.KerLatS.kerEntHyp_latS <;> assumption)
end
