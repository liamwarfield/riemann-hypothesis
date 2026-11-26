module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarStartConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLetterMulBoundedFactorMemNormalFormSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsPassGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsPassGenerators
namespace GlobalTheory.HatNF.GenMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {P : M.Par}

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem star_listProd (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, star_mul, ih, List.prod_append]

omit [StarModule ℂ A] in
theorem mem_span (d : Q.NFData P A) {b X : A} (hb : b ∈ bmon d) (hX : X ∈ hats d.L) :
    b * X ∈ nfSpan d (hats d.L) 0 0 1 := by
  unfold nfSpan
  refine Submodule.subset_span ⟨b, hb, [X], rfl, ?_⟩
  simp [hX]

omit [StarModule ℂ A] in
theorem kap_comm (d : Q.NFData P A) (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahatv y) ∧ Commute (d.κ f) (d.L.R0v y) := by
  obtain ⟨-, -, hR, -, -, -, hk⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nabs := hR.2.1 f _ (Or.inr (by simp))
  have hpb : ∀ l, Commute (d.κ f) (d.L.pb l) := fun l => hk f _ (by simp [TL.siteOps])
  obtain ⟨hA, hB⟩ := Formalism.FourierDecayAlt.P.MAx3.Q.comm_Tvprod d.L (d.κ f) hpb (fun l => hf _ (m_cb d.L l))
    (fun l => hf _ (m_cbi d.L l)) y
  have hA' : Commute (d.κ f) (d.L.Avr y) := hA
  have hB' : Commute (d.κ f) (d.L.Bvr y) := hB
  have hDr : Commute (d.κ f) d.L.Dr := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_c d.L l)
  have hDrb : Commute (d.κ f) d.L.Drb := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_cb d.L l)
  have hm : Commute (d.κ f) (d.L.m0 y) :=
    hn.neg_right.sub_right ((Algebra.commutes _ _).symm |> fun h : Commute (d.κ f) (algebraMap ℂ A (y - 1/2)) =>
      h.mul_right ((hf _ (m_ζ d.L)).mul_right (hf _ (m_GGi d.L))))
  exact ⟨hDrb.mul_right hA', (hDr.mul_right (hf _ (m_GG d.L))).mul_right ((hm.mul_right hA').add_right hB')⟩

omit [StarModule ℂ A] in
theorem ss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * ssn d i = ssn d i * d.L.Ahatv (Y - 1) ∧ d.L.R0v Y * ssn d i = ssn d i * d.L.R0v (Y - 1) := by
  obtain ⟨-, -, hR, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS i) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm)
    (fun l => (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).symm) (fun l => (hc _ (Or.inr ⟨l, rfl⟩)).symm) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) Y
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem sss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * star (ssn d i) = star (ssn d i) * d.L.Ahatv (Y + 1) ∧
      d.L.R0v Y * star (ssn d i) = star (ssn d i) * d.L.R0v (Y + 1) := by
  obtain ⟨-, hS, hR, sp, sc, sci, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  obtain ⟨sz, szb, szi, szbi, sg, sgi⟩ := Formalism.FourierDecayAlt.P.TLA.M2.star_fns d.L hS
  have sn : star d.L.nab = d.L.nabs := hS.2.1
  have sns : star d.L.nabs = d.L.nab := by rw [← sn, star_star]
  have scb : ∀ l, star (d.L.cb l) = d.L.c l := fun l => by rw [← sc, star_star]
  have scbi : ∀ l, star (d.L.cbi l) = d.L.ci l := fun l => by rw [← sci, star_star]
  have spb : ∀ l, star (d.L.pb l) = -d.L.p l := fun l => by
    rw [← star_star (d.L.p l), sp, star_neg, neg_neg]
  have sf : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
    intro x hx
    simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
    · rw [sc]; exact m_cb d.L l
    · rw [sci]; exact m_cbi d.L l
    · rw [scb]; exact m_c d.L l
    · rw [scbi]; exact m_ci d.L l
    · rw [sz]; exact m_ζb d.L
    · rw [szi]; exact m_ζbi d.L
    · rw [szb]; exact m_ζ d.L
    · rw [szbi]; exact m_ζi d.L
    · rw [sg]; exact m_GG d.L
    · rw [sgi]; exact m_GGi d.L
  have hf : ∀ x ∈ d.L.fns, Commute (star (d.SS i)) x := fun x hx => by
    have := (hc _ (Or.inl (Or.inl (sf x hx)))).star_star
    rwa [star_star] at this
  have hp : ∀ l, Commute (star (d.SS i)) (d.L.p l) := fun l => by
    have := (hc _ (Or.inr ⟨l, rfl⟩)).star_star
    rw [spb] at this
    exact Commute.neg_right_iff.1 this
  have hpb : ∀ l, Commute (star (d.SS i)) (d.L.pb l) := fun l => by
    have := (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).star_star
    rw [sp] at this
    exact Commute.neg_right_iff.1 this
  have c1 : star (d.SS i) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζb d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζb d.L)]
  have c2 : star (d.SS i) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζ d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζ d.L)]
  have k1 : d.L.nab * star (d.SS i) = star (d.SS i) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS i) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sns, sz, sgi] at this
    rw [← c1, this]; abel
  have k2 : d.L.nabs * star (d.SS i) = star (d.SS i) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS i) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sn, szb, sgi] at this
    rw [← c2, this]; abel
  have sDrb : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext scb
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_c d.L l)
  have sDri : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext sci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_cbi d.L l)
  have e : star (ssn d i) = star (d.SS i) * (d.L.Dr * d.L.Drbi) := by
    rw [ssn, star_mul, star_mul, sDrb, sDri, cl_comm d.L (memDrbi d.L) (memDr d.L)]
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS i)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) (fun x hx => (hf x hx).symm) (fun l => (hp l).symm)
    (fun l => (hpb l).symm) k1 k2 Y
  rw [e]
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

end

theorem minus_hats_pass_generators :
    ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d →
      ∀ b ∈ bset d, ∀ y : ℂ,
        d.L.Ahatv y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0v y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrv : d.L.Dr * d.L.Dbi ∈ bmon d := by
    rw [drv_eq]; exact Submonoid.mul_mem _ mDD mζi
  have sA : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.Ahatv y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inl (Or.inr ⟨y, rfl⟩))
  have sR : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.R0v y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inr ⟨y, rfl⟩)
  have hInv := Formalism.FourierDecayAlt.P.inverseCommutators _ P.r d.L y
  have hb' := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · rw [← hInv.2.2.2.2.2.1, ← hInv.2.2.2.2.2.2.1]
      exact ⟨sA hb' _, sR hb' _⟩
    · rw [← hInv.2.2.1, vgen_ζbi_R]
      refine ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) ?_⟩
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (sA mDD _))
        (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDD) _))
    · rw [vgen_DD_A, vgen_DD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDD hdrv) _))⟩
    · rw [vgen_DbD_A, vgen_DbD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDbD hdrv) _))⟩
  · rw [← (kap_comm d h f y).1.eq, ← (kap_comm d h f y).2.eq]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := ss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := sss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    simp only [] at hb' ⊢
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩

end GlobalTheory.HatNF.GenMinus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsPassGeneratorsStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ, d.L.Ahatv y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0v y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators | exact GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators | (intros; apply GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsPassGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsPassGenerators
namespace GlobalTheory.HatNF.GenPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem star_inv_eq {x xi y yi : A} (h : star x = y) (hx : x * xi = 1) (hy : y * yi = 1) : star xi = yi := by
  have h1 : star xi * y = 1 := by rw [← h, ← star_mul, hx, star_one]
  calc star xi = star xi * (y * yi) := by rw [hy, mul_one]
    _ = yi := by rw [← mul_assoc, h1, one_mul]

theorem star_list_prod (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.prod_cons, star_mul, ih, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]

variable {P : M.Par} {d : Q.NFData P A}

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ hats d.L) : b * h ∈ nfSpan d (hats d.L) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem ahat_mem (y : ℂ) : d.L.Ahat y ∈ hats d.L := Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
theorem plusHatR_mem_hatLettersAllPoints (y : ℂ) : d.L.R0 y ∈ hats d.L := Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))

theorem kappa_comm (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahat y) ∧ Commute (d.κ f) (d.L.R0 y) := by
  obtain ⟨-, -, hR, -, -, -, hs⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nab := hR.2.1 f _ (Or.inr (by simp))
  have hp : ∀ l, Commute (d.κ f) (d.L.p l) := fun l => hs f _ (by simp [TL.siteOps])
  have hT := d.L.inv_comm_Tprod hp (fun l => hf _ (d.L.inv_mem_c l)) (fun l => hf _ (d.L.inv_mem_ci l)) y
  have hDr : Commute (d.κ f) d.L.Dr := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_c l)
  have hDrb : Commute (d.κ f) d.L.Drb := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_cb l)
  have hl0 : Commute (d.κ f) (d.L.l0 y) :=
    hn.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
      ((hf _ d.L.inv_mem_ζb).mul_right (hf _ d.L.inv_mem_GGi)))
  exact ⟨hDr.mul_right (hT 0 0),
    (hDrb.mul_right (hf _ d.L.inv_mem_GG)).mul_right ((hl0.mul_right (hT 0 0)).add_right (hT 1 0))⟩

theorem ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * ssn d l = ssn d l * d.L.Ahat (y - 1) ∧ d.L.R0 y * ssn d l = ssn d l * d.L.R0 (y - 1) := by
  obtain ⟨-, -, hR, -, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS l) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm.eq)
    (fun m => (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).symm.eq) (fun m => (hc _ (Or.inr ⟨m, rfl⟩)).symm.eq) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) y
  exact ⟨this.1, this.2.1⟩

variable [StarModule ℂ A]

theorem star_GG (h : HatHyp d) : star d.L.GG = d.L.GG := by
  obtain ⟨-, ⟨hz, -, hT⟩, -⟩ := h
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  rw [d.L.GG_def, star_sub, star_mul, hz, hzb, Algebra.algebraMap_eq_smul_one, star_smul, hT, star_one]

theorem star_GGi (h : HatHyp d) : star d.L.GGi = d.L.GGi := star_inv_eq (star_GG h) d.L.GG_GGi d.L.GG_GGi

theorem star_fns (h : HatHyp d) : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
  have hG := star_GG h
  have hGi := star_GGi h
  obtain ⟨-, ⟨hz, -, -⟩, -, -, hc, hci, -⟩ := h
  have hzi : star d.L.ζi = d.L.ζbi := star_inv_eq hz d.L.ζ_ζi d.L.ζb_ζbi
  intro x hx
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
  · rw [hc]; exact d.L.inv_mem_cb l
  · rw [hci]; exact d.L.inv_mem_cbi l
  · rw [← hc, star_star]; exact d.L.inv_mem_c l
  · rw [← hci, star_star]; exact d.L.inv_mem_ci l
  · rw [hz]; exact d.L.inv_mem_ζb
  · rw [hzi]; exact d.L.inv_mem_ζbi
  · rw [← hz, star_star]; exact d.L.inv_mem_ζ
  · rw [← hzi, star_star]; exact d.L.inv_mem_ζi
  · rw [hG]; exact d.L.inv_mem_GG
  · rw [hGi]; exact d.L.inv_mem_GGi

omit [StarModule ℂ A] in
theorem star_ssn (h : HatHyp d) (l : ℕ) : star (ssn d l) = star (d.SS l) * (d.L.Dr * d.L.Drbi) := by
  obtain ⟨-, -, -, -, hc, hci, -⟩ := h
  have h1 : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext fun m => by rw [Function.comp, ← hc, star_star]
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_c m)
  have h2 : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext hci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_cbi m)
  unfold ssn
  rw [star_mul, star_mul, h1, h2, cl_comm d.L (memDrbi d.L) (memDr d.L)]

theorem star_ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * star (ssn d l) = star (ssn d l) * d.L.Ahat (y + 1) ∧
      d.L.R0 y * star (ssn d l) = star (ssn d l) * d.L.R0 (y + 1) := by
  have hGi := star_GGi h
  have hF := star_fns h
  rw [star_ssn h]
  obtain ⟨-, ⟨hz, hn, -⟩, hR, hp, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  have hns : star d.L.nabs = d.L.nab := by rw [← hn, star_star]
  have key : ∀ x, Commute (d.SS l) (star x) → x * star (d.SS l) = star (d.SS l) * x := fun x hx => by
    have := congrArg star hx.eq
    simpa [star_mul] using this
  have hf : ∀ x ∈ d.L.fns, x * star (d.SS l) = star (d.SS l) * x :=
    fun x hx => key x (hc _ (Or.inl (Or.inl (hF x hx))))
  have hp1 : ∀ m, d.L.p m * star (d.SS l) = star (d.SS l) * d.L.p m := fun m =>
    key _ (by rw [hp]; exact (hc _ (Or.inr ⟨m, rfl⟩)).neg_right)
  have hp2 : ∀ m, d.L.pb m * star (d.SS l) = star (d.SS l) * d.L.pb m := fun m =>
    key _ (by
      have : star (d.L.pb m) = -d.L.p m := by
        have := congrArg star (hp m)
        rw [star_star, star_neg] at this
        rw [this, neg_neg]
      rw [this]; exact (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).neg_right)
  have c1 : star (d.SS l) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζb, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζb).eq]
  have c2 : star (d.SS l) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζ, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζ).eq]
  have e1 : d.L.nab * star (d.SS l) = star (d.SS l) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS l) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hns, hz, hGi] at this
    rw [← c1, this]; abel
  have e2 : d.L.nabs * star (d.SS l) = star (d.SS l) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS l) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hn, hzb, hGi] at this
    rw [← c2, this]; abel
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS l)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) hf hp1 hp2 e1 e2 y
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2.1⟩

end

theorem plus_hats_pass_generators : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ,
      d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrb : d.L.Drb * d.L.Di ∈ bmon d := by
    rw [drb_eq]; exact Submonoid.mul_mem _ mDbD mζbi
  have hbm := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · refine ⟨by rw [(hat_ζi d.L y).1]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_ζi_R]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _)) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (mem_span mDbD (ahat_mem _)))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDbD) (ahat_mem _))))
    · exact ⟨by rw [← (hat_ζbi d.L y).1]; exact mem_span hbm (ahat_mem _),
        by rw [← (hat_ζbi d.L y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
    · refine ⟨by rw [gen_DD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDD hdrb) (ahat_mem _)))
    · refine ⟨by rw [gen_DbD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DbD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDbD hdrb) (ahat_mem _)))
  · exact ⟨by rw [← (kappa_comm h f y).1.eq]; exact mem_span hbm (ahat_mem _),
      by rw [← (kappa_comm h f y).2.eq]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by rw [(ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by rw [(ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by beta_reduce; rw [(star_ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by beta_reduce; rw [(star_ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩

end GlobalTheory.HatNF.GenPlus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsPassGeneratorsStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ, d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | exact GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | (intros; apply GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLetterMulBoundedFactorMemNormalFormSpan
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem bmon_mul_mem_nfSpan_of_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {c : A} (hc : c ∈ bmon d)
    {x : A} (hx : x ∈ nfSpan d T i j n) : c * x ∈ nfSpan d T i j n := by
  unfold nfSpan at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, H, hHl, hH, hrest⟩ := hy
    have e : c * y = (c * b) * d.L.Di ^ i * TL.gI d.L ^ j * H.prod := by
      rw [hrest]; simp only [mul_assoc]
    rw [e]
    exact Submodule.subset_span ⟨c * b, mul_mem hc hb, H, hHl, hH, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy

theorem nfSpan_one_mul_mem_of_letters (d : Q.NFData P A) (T : Set A) {c : A}
    (hc : ∀ X ∈ T, X * c ∈ nfSpan d T 0 0 1) {x : A} (hx : x ∈ nfSpan d T 0 0 1) :
    x * c ∈ nfSpan d T 0 0 1 := by
  unfold nfSpan at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, H, hHl, hH, hrest⟩ := hy
    rcases H with _ | ⟨h, _ | ⟨h', t⟩⟩
    · simp at hHl
    · have hhT : h ∈ T := hH h (by simp)
      have e : y * c = b * (h * c) := by
        rw [hrest]; simp [mul_assoc]
      rw [e]
      exact bmon_mul_mem_nfSpan_of_mem d T 0 0 1 hb (hc h hhT)
    · simp at hHl
  | zero => simp
  | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hy

end

theorem hats_mul_bmon_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ X ∈ hats d.L, ∀ b ∈ bmon d, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d hd X hX b hb
  have key : ∀ X ∈ hats d.L, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
    clear hX X
    unfold bmon at hb
    induction hb using Submonoid.closure_induction with
    | mem b hb =>
      intro X hX
      rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
      · exact (GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats P A d hd b hb y).1
      · exact (GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats P A d hd b hb y).2
      · exact (GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats P A d hd b hb y).1
      · exact (GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats P A d hd b hb y).2
    | one =>
      intro X hX
      exact Submodule.subset_span ⟨1, one_mem _, [X], rfl, by simpa using hX, by simp⟩
    | mul b₁ b₂ _ _ h₁ h₂ =>
      intro X hX
      rw [← mul_assoc]
      exact nfSpan_one_mul_mem_of_letters d _ h₂ (h₁ X hX)
  exact key X hX

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLetterMulBoundedFactorMemNormalFormSpanStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetter_mul_boundedFactor_mem_normalFormSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ X ∈ hats d.L, ∀ b ∈ bmon d, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan | exact GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosed
namespace GlobalTheory.HatNF.SpanMul

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem gen_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) (H : List A)
    (hl : H.length = n) (hT : ∀ h ∈ H, h ∈ T) :
    b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod ∈ nfSpan d T i j n :=
  Submodule.subset_span ⟨b, hb, H, hl, hT, rfl⟩

theorem map_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) (f : A →ₗ[ℂ] A) (S : Submodule ℂ A)
    (h : ∀ b ∈ bmon d, ∀ H : List A, H.length = n → (∀ h ∈ H, h ∈ T) →
      f (b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod) ∈ S) :
    ∀ x ∈ nfSpan d T i j n, f x ∈ S := by
  have : nfSpan d T i j n ≤ S.comap f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hl, hT, rfl⟩
    exact h b hb H hl hT
  exact fun x hx => this hx

theorem bdd_mul (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) :
    ∀ x ∈ nfSpan d T i j n, b * x ∈ nfSpan d T i j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ b) _ ?_
  intro b' hb' H hl hT
  have := gen_mem d T i j n ((bmon d).mul_mem hb hb') H hl hT
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di * x ∈ nfSpan d T (i + 1) j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ d.L.Di) _ ?_
  intro b hb H hl hT
  have := gen_mem d T (i + 1) j n hb H hl hT
  rw [pow_succ', ← mul_assoc b, (hD b hb).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem gi_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L * x ∈ nfSpan d T i (j + 1) n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ (TL.gI d.L)) _ ?_
  intro b hb H hl hT
  have := gen_mem d T i (j + 1) n hb H hl hT
  rw [pow_succ', ← mul_assoc (b * _), ((hG b hb).mul_left (hDG.pow_left i)).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_pow_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di ^ k * x ∈ nfSpan d T (i + k) j n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact di_mul d hD T _ j n _ ih

theorem gi_pow_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L ^ k * x ∈ nfSpan d T i (j + k) n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact gi_mul d hG hDG T i _ n _ ih

theorem one_letter_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di)
    (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L)) (hDG : Commute d.L.Di (TL.gI d.L)) (T T' : Set A)
    (i₀ j₀ n i j : ℕ) (u : A) (hu : ∀ X ∈ T', X * u ∈ nfSpan d T i₀ j₀ n) :
    ∀ x ∈ nfSpan d T' i j 1, x * u ∈ nfSpan d T (i₀ + i) (j₀ + j) n := by
  refine map_mem d T' i j 1 (LinearMap.mulRight ℂ u) _ ?_
  intro b hb H hl hT
  obtain ⟨X, rfl⟩ := List.length_eq_one_iff.1 hl
  have := bdd_mul d T _ _ n hb _ (di_pow_mul d hD T _ _ n i _
    (gi_pow_mul d hG hDG T _ _ n j _ (hu X (hT X (by simp)))))
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_cons, List.prod_nil, mul_one] using this

theorem mul_prod (d : Q.NFData P A) (T : Set A) (i j m : ℕ) (H : List A) (hT : ∀ h ∈ H, h ∈ T) :
    ∀ x ∈ nfSpan d T i j m, x * H.prod ∈ nfSpan d T i j (H.length + m) := by
  refine map_mem d T i j m (LinearMap.mulRight ℂ H.prod) _ ?_
  intro b hb H' hl hT'
  have := gen_mem d T i j (H.length + m) hb (H' ++ H) (by simp [hl, add_comm]) (by
    intro h hh
    rcases List.mem_append.1 hh with h1 | h1
    · exact hT' h h1
    · exact hT h h1)
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_append] using this

theorem span_mul : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ T : Set A, (∀ i j n, ∀ x ∈ nfSpan d T i j n, (∀ b ∈ bmon d, b * x ∈ nfSpan d T i j n) ∧ d.L.Di * x ∈ nfSpan d T (i + 1) j n ∧ TL.gI d.L * x ∈ nfSpan d T i (j + 1) n) ∧ ∀ a : ℕ, (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ i j n, ∀ X ∈ hats d.L, ∀ x ∈ nfSpan d T i j n, X * x ∈ nfSpan d T i (j + a) (n + 1) := by
  intro P A _ _ _ _ d hd T
  have h1 := GlobalTheory.T.hatLetter_mul_boundedFactor_mem_normalFormSpan P A d hd
  obtain ⟨h2, h3, hDG⟩ := GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors P A d hd
  have hD : ∀ b ∈ bmon d, Commute b d.L.Di := fun b hb => (h3 b hb).2.1
  have hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L) := fun b hb => (h3 b hb).2.2.1
  refine ⟨fun i j n x hx => ⟨fun b hb => bdd_mul d T i j n hb x hx, di_mul d hD T i j n x hx,
    gi_mul d hG hDG T i j n x hx⟩, ?_⟩
  intro a ha i j n X hX
  refine map_mem d T i j n (LinearMap.mulLeft ℂ X) _ ?_
  intro b hb H hl hT
  have e1 : ∀ k, X * b * d.L.Di ^ k ∈ nfSpan d (hats d.L) k 0 1 := by
    intro k
    induction k with
    | zero => simpa using h1 X hX b hb
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 1 0 1 k 0 _ (fun Y hY => (h2 Y hY).1) _ ih
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e2 : ∀ k, X * b * d.L.Di ^ i * TL.gI d.L ^ k ∈ nfSpan d (hats d.L) i k 1 := by
    intro k
    induction k with
    | zero => simpa using e1 i
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 0 1 1 i k _ (fun Y hY => (h2 Y hY).2) _ ih
      rw [zero_add] at this
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e3 := one_letter_mul d hD hG hDG T _ 0 a (H.length + 1) i j H.prod
    (fun Y hY => mul_prod d T 0 a 1 H hT Y (ha Y hY)) _ (e2 j)
  rw [zero_add, hl, add_comm a j] at e3
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using e3

end GlobalTheory.HatNF.SpanMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosedStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalFormProductSpan_left_mul_closed : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ T : Set A, (∀ i j n, ∀ x ∈ nfSpan d T i j n, (∀ b ∈ bmon d, b * x ∈ nfSpan d T i j n) ∧ d.L.Di * x ∈ nfSpan d T (i + 1) j n ∧ TL.gI d.L * x ∈ nfSpan d T i (j + 1) n) ∧ ∀ a : ℕ, (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ i j n, ∀ X ∈ hats d.L, ∀ x ∈ nfSpan d T i j n, X * x ∈ nfSpan d T i (j + a) (n + 1) := by
  first | exact @GlobalTheory.HatNF.SpanMul.span_mul | exact GlobalTheory.HatNF.SpanMul.span_mul | (intros; apply GlobalTheory.HatNF.SpanMul.span_mul <;> assumption)
end
