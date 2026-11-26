module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjEntrySmulCapelliEigenSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EnergyBoundPolynomialWeightPowCapelliEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPowSmulCompPolyFamilyEigenSu
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialSmulCapelliEigenfunctionSum
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.EigenSumPoly

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def IsEigenSum (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ),
    (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧
    (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧
    (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g =
      ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧
    ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g

def entryVar (g : B.Mat k r) :
    (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

end

end GlobalTheory.EigenSumPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPowSmulCompPolyFamilyEigenSu
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

private lemma CV_comp_clm_eq_clm_CV {k r : ℕ} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (Φ : E →L[ℂ] E') (Y : ℂ) {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → E}
    (hf : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) f) {g : _root_.Formalism.FourierDecayAlt.B.Mat k r} (hg : g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r) :
    _root_.Formalism.FourierDecayAlt.Q.CV k r Y (fun h => Φ (f h)) g = Φ (_root_.Formalism.FourierDecayAlt.Q.CV k r Y f g) := by
  have hs : _root_.Formalism.FourierDecayAlt.Q.SmoothLev k r 0 Set.univ f := by
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hEq⟩ := hf g₀ hg₀.1.1
    exact ⟨U, F, hU, hgU, hF, fun g hg hg' => hEq g hg hg'.1⟩
  have hg0 : g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r 0 := ⟨hg, fun a ha => (Nat.not_lt_zero _ ha).elim⟩
  exact _root_.Formalism.FourierDecayAlt.Q.TPresMain.qminor_clm (i := 0) (D := Set.univ) isOpen_univ id id (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 Y) Φ f hs g ⟨hg0, trivial⟩

private lemma entry_smul_eigenfunction_lemma_6 {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (ν : Fin (2 * r + k + 1) → ℤ) (i j : Fin (2 * r + k + 1))
    (f : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp))
    (hgap : ∀ s t, s ≠ t → 2 * (d : ℝ) < |lam s - lam t|) (hν : ∀ s, |ν s| ≤ (d : ℤ))
    (hck : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) f) (hcc : ∀ m : ℕ, _root_.Formalism.FourierDecayAlt.B.InCC A m f)
    (heig : ∀ Y : ℝ, ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.FourierDecayAlt.Q.CV k r (Y : ℂ) f g =
      ((∏ s, (Y + lam s + (ν s : ℝ)) : ℝ) : ℂ) • f g) :
    _root_.GlobalTheory.EigenSumPoly.IsEigenSum (Wp := Wp) (Wq := Wq) lam (d + 1) (A - 1) (fun g => g i j • f g) := by
  obtain ⟨V, W, _, _, _, _, E, E', ι, ev, mul, hGl, hGl', hι, hW, hCk, hinj, hInCC, hrep, hE, hCV, hmul⟩ :=
    _root_.GlobalTheory.capelli_module_model k r Wp Wq (fun s => lam s + ν s) A
  obtain ⟨w, hw⟩ := hrep f ⟨hck, hcc⟩ (fun Y g hg => by rw [heig Y g hg]; simp [add_assoc])
  have hsm : ∀ a : Fin (2 * r + k + 1), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => g i a) :=
    fun a => _root_.PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_entry i a)
  have hEH : ∀ (a b c : Fin (2 * r + k + 1)) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r),
      _root_.Formalism.FourierDecayAlt.Q.EH k r a b (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => g i c) g = if b = c then g i a else 0 := by
    intro a b c g
    have h := _root_.Formalism.FourierDecayAlt.P.Qx5.eh_linear (Matrix.entryLinearMap ℂ ℂ i c) g a b
    simp only [Matrix.entryLinearMap_apply] at h
    rw [h]
    erw [Matrix.mul_apply]
    by_cases hbc : b = c <;> simp [hbc, Matrix.single_apply]
  set x : Fin (2 * r + k + 1) → Module.End ℂ V := fun a => mul (fun g => g i a) with hx
  have hcomm : ∀ a b c, E a b * x c = x c * E a b + if b = c then x a else 0 := by
    intro a b c
    apply LinearMap.ext
    intro v
    apply hinj
    intro g hg
    have h1 := (hmul _ (hsm c)).2 a b v g hg
    have h2 := (hmul _ (hsm c)).1 ((E a b) v) g hg
    rw [Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply, map_add (f := _), Pi.add_apply, h1, h2, hEH]
    split_ifs with hbc
    · subst hbc
      have h3 := (hmul _ (hsm a)).1 v g hg
      try simp only at h3
      rw [h3]
    · simp
  set μ : Fin (2 * r + k + 1) → ℂ := fun s => ((lam s + ν s : ℝ) : ℂ) - (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 with hμ
  have hinjμ : Function.Injective μ := by
    intro s t hst
    by_contra hne
    have h1 : ((lam s + ν s : ℝ) : ℂ) = ((lam t + ν t : ℝ) : ℂ) := by simpa [hμ] using hst
    have h2 : lam s + ν s = lam t + ν t := by exact_mod_cast h1
    have hs' : |(ν s : ℝ)| ≤ d := by exact_mod_cast hν s
    have ht' : |(ν t : ℝ)| ≤ d := by exact_mod_cast hν t
    have h3 : |lam s - lam t| ≤ 2 * d := by
      rw [abs_le] at hs' ht' ⊢
      constructor <;> linarith
    linarith [hgap s t hne]
  obtain ⟨v, hv, hveig⟩ := _root_.GlobalTheory.qdet_vector_multiplier_shift_plus V W (2 * r + k + 1) E E' ι x μ hGl hGl' hι
    hinjμ (fun u w => by simpa [hμ] using hW u w) hcomm j w
  refine ⟨2 * r + k + 1, fun s => ev (∑ a, x a (ι (v s a))), fun s t => ν t + if t = s then 1 else 0,
    ?_, ?_, ?_, ?_⟩
  · intro s t
    have := hν t
    show |ν t + (if t = s then 1 else 0)| ≤ ((d + 1 : ℕ) : ℤ)
    rw [abs_le] at this ⊢
    split_ifs <;> push_cast <;> constructor <;> omega
  · intro s
    refine ⟨hCk _, fun m => ?_⟩
    have hcong : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => ∑ a, g i a • ev (ι (v s a)) g) g =
        ev (∑ a, x a (ι (v s a))) g := by
      intro g hg
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h3 := (hmul _ (hsm a)).1 (ι (v s a)) g hg
      try simp only at h3
      rw [hx, h3]
    refine (_root_.GlobalTheory.ckOn_inCC_congr_on_group k r _ (A - 1) _ _ hcong).2 m ?_
    have hl := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum (A := A - 1) (m := m) (List.finRange (2 * r + k + 1))
      (fun a (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) => g i a • ev (ι (v s a)) g) (fun a _ => by
        have hpd : ∀ (A' : ℝ) (m' : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (b : ℝ),
            _root_.Formalism.FourierDecayAlt.B.CCle (A' + ((1 : ℕ) : ℝ)) m' F b → _root_.Formalism.FourierDecayAlt.B.CCle A' m' (fun g => g i a • F g) (K * b) :=
          @And.right (∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F →
            _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) fun g => g i a • F g) _
            (_root_.Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (Wp := Wp) (Wq := Wq) (k := k) (r := r) (c := fun g => g i a) (_root_.Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_entry i a))
        obtain ⟨K, -, hK⟩ := hpd (A - 1) m
        obtain ⟨b, hb⟩ := hInCC (v s a) m
        refine ⟨K * b, hK _ b ?_⟩
        rw [show A - 1 + ((1 : ℕ) : ℝ) = A by push_cast; ring]
        exact hb)
    convert hl using 1
    funext g
    exact Fin.sum_univ_def _
  · intro s Y g hg
    rw [← hCV (Y : ℂ) _ g hg, hveig s, map_smul, Pi.smul_apply]
    congr 1
    push_cast
    refine Finset.prod_congr rfl fun t _ => ?_
    simp only [hμ]
    split_ifs <;> push_cast <;> ring
  · intro g hg
    have h3 := (hmul _ (hsm j)).1 (ι w) g hg
    try simp only at h3
    show g i j • f g = _
    rw [← hw g hg, ← h3]
    show ev (x j (ι w)) g = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv, map_sum, Finset.sum_apply]

private lemma isEigenSum_entry_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (i j : Fin (2 * r + k + 1))
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hgap : ∀ s t, s ≠ t → 2 * (d : ℝ) < |lam s - lam t|)
    (hF : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam d A F) : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + 1) (A - 1) (fun g => g i j • F g) := by
  obtain ⟨N₀, Fi, ν, hν, hreg, heig, hsum⟩ := hF
  exact _root_.GlobalTheory.capelli_eigenSum_linearCombination k r Wp Wq lam (d + 1) (A - 1) (Fin N₀) Finset.univ (fun _ => 1)
    (fun l g => g i j • Fi l g) _
    (fun l _ => ⟨d + 1, A - 1, le_rfl, le_rfl, entry_smul_eigenfunction_lemma_6 lam d A (ν l) i j (Fi l) hgap (hν l)
      (hreg l).1 (hreg l).2 (heig l)⟩)
    (fun g hg => by simp [hsum g hg, Finset.smul_sum])

private lemma isEigenSum_star_entry_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (i j : Fin (2 * r + k + 1))
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hgap : ∀ s t, s ≠ t → 2 * (d : ℝ) < |lam s - lam t|)
    (hF : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam d A F) : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + 1) (A - 1) (fun g => star (g i j) • F g) :=
  _root_.GlobalTheory.conj_entry_smul_eigenSum k r Wp Wq lam d A i j F hgap hF

private lemma monomial_smul_eigenSum_lemma_3 {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ)
    (s : Multiset ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)))) :
    ∀ (d : ℕ) (A : ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)),
      (∀ s' t, s' ≠ t → 2 * ((d + Multiset.card s : ℕ) : ℝ) < |lam s' - lam t|) → _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam d A F →
      _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + Multiset.card s) (A - Multiset.card s)
        (fun g => (s.map (_root_.GlobalTheory.EigenSumPoly.entryVar g)).prod • F g) := by
  induction s using Multiset.induction_on with
  | empty =>
    intro d A F _ hF
    simpa using hF
  | cons a s ih =>
    intro d A F hgap hF
    have hgap' : ∀ s' t, s' ≠ t → 2 * ((d + Multiset.card s : ℕ) : ℝ) < |lam s' - lam t| := by
      intro s' t hst
      refine lt_of_le_of_lt ?_ (hgap s' t hst)
      simp only [Multiset.card_cons]
      push_cast
      linarith
    have h1 := ih d A F hgap' hF
    have h2 : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + Multiset.card s + 1) (A - Multiset.card s - 1)
        (fun g => _root_.GlobalTheory.EigenSumPoly.entryVar g a • (s.map (_root_.GlobalTheory.EigenSumPoly.entryVar g)).prod • F g) := by
      rcases a with ⟨i, j⟩ | ⟨i, j⟩
      · exact isEigenSum_entry_smul lam _ _ i j _ hgap' h1
      · exact isEigenSum_star_entry_smul lam _ _ i j _ hgap' h1
    have e1 : d + Multiset.card (a ::ₘ s) = d + Multiset.card s + 1 := by
      simp [Multiset.card_cons, add_assoc]
    have e2 : A - ((Multiset.card (a ::ₘ s) : ℕ) : ℝ) = A - Multiset.card s - 1 := by
      simp only [Multiset.card_cons]
      push_cast
      ring
    rw [e1, e2]
    convert h2 using 2 with g
    rw [Multiset.map_cons, Multiset.prod_cons, mul_smul]

private lemma isEigenSum_poly_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (lam : Fin (2 * r + k + 1) → ℝ) (d e : ℕ) (A : ℝ) (c : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ) (hc : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg e c)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hgap : ∀ s t, s ≠ t → 2 * ((d + e : ℕ) : ℝ) < |lam s - lam t|)
    (hF : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam d A F) : _root_.GlobalTheory.EigenSumPoly.IsEigenSum lam (d + e) (A - e) (fun g => c g • F g) := by
  classical
  obtain ⟨q, hq, hcq⟩ := hc
  refine _root_.GlobalTheory.capelli_eigenSum_linearCombination k r Wp Wq lam (d + e) (A - e) _ q.support q.coeff
    (fun m g => (m.toMultiset.map (_root_.GlobalTheory.EigenSumPoly.entryVar g)).prod • F g) _ (fun m hm => ?_) (fun g _ => ?_)
  · have hcard : Multiset.card m.toMultiset ≤ e := by
      rw [Finsupp.card_toMultiset]
      exact (MvPolynomial.le_totalDegree hm).trans hq
    refine ⟨d + Multiset.card m.toMultiset, A - Multiset.card m.toMultiset, by omega, ?_,
      monomial_smul_eigenSum_lemma_3 lam m.toMultiset d A F (fun s t hst => lt_of_le_of_lt ?_ (hgap s t hst)) hF⟩
    · have : (Multiset.card m.toMultiset : ℝ) ≤ e := by exact_mod_cast hcard
      linarith
    · have : ((d + Multiset.card m.toMultiset : ℕ) : ℝ) ≤ ((d + e : ℕ) : ℝ) := by
        exact_mod_cast (by omega : d + Multiset.card m.toMultiset ≤ d + e)
      linarith
  · show c g • F g = _
    rw [hcq g, MvPolynomial.eval_eq, Finset.sum_smul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    rfl

theorem _root_.GlobalTheory.gfPow_smul_comp_polyOp_eigenSum :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (lam : Fin (2 * r + k + 1) → ℝ) (A₀ : ℝ) (p₀ dA : ℕ) (f : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (Aop : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq' →L[ℂ] Wq)), (∀ s t, s ≠ t → 2 * (((2 * r + 2) * p₀ + dA : ℕ) : ℝ) < |lam s - lam t|) → (_root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (f) ∧ ∀ m : ℕ, _root_.Formalism.FourierDecayAlt.B.InCC (A₀) m (f)) → (∀ Y : ℝ, ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.FourierDecayAlt.Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → (∃ (n₁ : ℕ) (c : Fin n₁ → _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq' →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ (((2 * r + 2) * p₀ + dA : ℕ) : ℤ)) ∧ (∀ i, (_root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (Fi i) ∧ ∀ m : ℕ, _root_.Formalism.FourierDecayAlt.B.InCC (A₀ - (((2 * r + 2) * p₀ + dA : ℕ) : ℝ)) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.FourierDecayAlt.Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, (fun g => ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ Wq' _ _ _ z z' lam A₀ p₀ dA f Aop hgap hf heig hA
  obtain ⟨hck, hcc⟩ := hf
  obtain ⟨n₁, c, L, hc, hAop⟩ := hA
  set e := (2 * r + 2) * p₀ + dA with he
  have hpiece : ∀ i, _root_.GlobalTheory.EigenSumPoly.IsEigenSum (Wp := Wp) (Wq := Wq') lam e (A₀ - e)
      (fun g => (((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) * c i g) • (f g).comp (L i)) := by
    intro i
    let Φ : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (L i)
    have hΦ : ∀ h, Φ h = h.comp (L i) := fun h => rfl
    have h0 : _root_.GlobalTheory.EigenSumPoly.IsEigenSum (Wp := Wp) (Wq := Wq') lam 0 A₀ (fun g => (f g).comp (L i)) := by
      refine ⟨1, fun _ g => (f g).comp (L i), fun _ _ => 0, fun _ _ => by simp, fun _ => ⟨?_, fun m => ?_⟩,
        fun _ Y g hg => ?_, fun g _ => by simp⟩
      · exact _root_.Formalism.FourierDecayAlt.P.CutBPEq.ckOn_clm Φ hck
      · obtain ⟨b, hb⟩ := hcc m
        exact ⟨_, _root_.Formalism.FourierDecayAlt.P.CutBPEq.ccle_clm Φ hb⟩
      · have h1 := CV_comp_clm_eq_clm_CV Φ (Y : ℂ) hck hg
        simp only [hΦ] at h1
        rw [h1, heig Y g hg]
        simp
    have hG := _root_.Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_prod (Finset.range p₀) (P := fun _ (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) => ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g : ℝ) : ℂ))
      (fun _ _ => _root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.gf_pd k r z z')
    have hfun : (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) * c i g) =
        fun g => (∏ _ ∈ Finset.range p₀, ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g : ℝ) : ℂ)) * c i g := by
      funext g
      simp
    have hpoly : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg e (fun g : _root_.Formalism.FourierDecayAlt.B.Mat k r => ((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) * c i g) := by
      rw [hfun, show e = (Finset.range p₀).card * (2 * r + 2) + dA by rw [he, Finset.card_range]; ring]
      exact _root_.Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul hG (hc i)
    have h2 := isEigenSum_poly_smul lam 0 e A₀ _ hpoly _ (fun s t h => by rw [zero_add]; exact hgap s t h) h0
    rw [zero_add] at h2
    exact h2
  exact _root_.GlobalTheory.capelli_eigenSum_linearCombination k r Wp Wq' lam e (A₀ - e) (Fin n₁) Finset.univ (fun _ => 1)
    (fun i g => (((_root_.Formalism.QuantumDeterminants.Gf k r z z' g ^ p₀ : ℝ) : ℂ) * c i g) • (f g).comp (L i)) _
    (fun i _ => ⟨e, A₀ - e, le_rfl, le_rfl, hpiece i⟩)
    (fun g _ => by
      ext v
      simp [hAop, Finset.smul_sum, smul_smul])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPowSmulCompPolyFamilyEigenSuStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliEigenfunction_pow_smul_comp_polyFamily_eigenSum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (lam : Fin (2 * r + k + 1) → ℝ) (A₀ : ℝ) (p₀ dA : ℕ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (Aop : B.Mat k r → (Wq' →L[ℂ] Wq)), (∀ s t, s ≠ t → 2 * (((2 * r + 2) * p₀ + dA : ℕ) : ℝ) < |lam s - lam t|) → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A₀) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat k r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq' →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ (((2 * r + 2) * p₀ + dA : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A₀ - (((2 * r + 2) * p₀ + dA : ℕ) : ℝ)) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (fun g => ((Gf k r z z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) g = ∑ i, Fi i g) := by
  first | exact @GlobalTheory.gfPow_smul_comp_polyOp_eigenSum | exact GlobalTheory.gfPow_smul_comp_polyOp_eigenSum | (intros; apply GlobalTheory.gfPow_smul_comp_polyOp_eigenSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormLeNormCOfEigenSum
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyLeOfEigenSum
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaCapelliSymmOfXiExists
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.BetaSym

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity MeasureTheory
open scoped ContDiff ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem clause_bdd (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : 0 ≤ A) (hCC : CCIntegrable D A)
    (Θ : DiffOp k r Wp Wq) (hS : SmoothCoef (GV k r) Θ)
    (hP : ∀ T ∈ Θ, ∃ C : ℝ, ∀ (u v : List (Mat k r)) (g : Mat k r),
      ‖dLR u v T.coef g‖ ≤ C ∧ ‖dLR u v T.coefAdj g‖ ≤ C)
    (F F' : Mat k r → (Wq →L[ℂ] Wp)) (hF0 : InCC A (opOrder Θ + 5) F) (hF0' : InCC A (opOrder Θ + 5) F') :
    InCC A 5 (opApply Θ F) ∧ InCC A 5 (opAdj Θ F') ∧ IntClause D Θ F F' := by
  have hF : InCC (A + 0) (opOrder Θ + 5) F := by rwa [add_zero]
  have hF' : InCC (A + 0) (opOrder Θ + 5) F' := by rwa [add_zero]
  have hO : IsOpen (∅ : Set (Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ GV k r, g ∈ (∅ : Set (Mat k r)) ∨ g ∈ GV k r := fun g hg => Or.inr hg
  have hAd0 : 0 ≤ A + 0 := by linarith
  have hadj : ∀ T ∈ Θ, InCC A (opOrder Θ + 5) (ap T.coefAdj F') := by
    intro T hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c', hc'⟩ := hF'
    exact ⟨_, prodBound (C := C) hO hcov (sCkOn_mono le_top (hS T hT).2)
      (fun u v _ _ _ g _ _ => by rw [Real.rpow_zero, mul_one]; exact (hC u v g).2) hc'
      (fun g _ h => absurd h (Set.notMem_empty g))⟩
  refine ⟨?_, ?_, ?_⟩
  · refine InCC_opsum Θ (fun T => ap T.coef (Rw T.word F)) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c, hc⟩ : InCC (A + 0) 5 (Rw T.word F) :=
      InCC_Rw T.word_lie (sInCC_mono le_rfl (by omega) hF)
    exact ⟨_, prodBound (C := C) hO hcov (sCkOn_mono le_top (hS T hT).1)
      (fun u v _ _ _ g _ _ => by rw [Real.rpow_zero, mul_one]; exact (hC u v g).1) hc
      (fun g _ h => absurd h (Set.notMem_empty g))⟩
  · refine InCC_opsum Θ
      (fun T => fun g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (ap T.coefAdj F') g) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨c, hc⟩ : InCC A 5 (Rw T.word.reverse (ap T.coefAdj F')) :=
      InCC_Rw (fun X hX => T.word_lie X (List.mem_reverse.mp hX))
        (sInCC_mono le_rfl (by simp; omega) (hadj T hT))
    exact ⟨_, CCle_smul _ hc⟩
  · intro p hp T hT i j hij hj
    have hlen := word_le_order Θ hT
    set a : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hadef
    set b : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hbdef
    have ha : a ∈ GV k r := gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)
    have hb : b ∈ GV k r := gv_mul hp.2.2.2.1 hp.2.2.1.1
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    have hl1 : (T.word.take i).reverse.length ≤ opOrder Θ := by
      simp only [List.length_reverse, List.length_take]; omega
    have hl2 : (T.word.drop j).length ≤ opOrder Θ := by
      simp only [List.length_drop]; omega
    obtain ⟨K₁, hK₁⟩ : InCC A 0 (Rw (T.word.take i).reverse (ap T.coefAdj F')) :=
      InCC_Rw hlie1 (sInCC_mono le_rfl (by omega) (hadj T hT))
    obtain ⟨K₂, hK₂⟩ : InCC (A + 0) 0 (Rw ((T.word.drop j).map fun X => b⁻¹ * X * b) F) :=
      InCC_Rw (fun X hX => by
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
        exact lie_conj (hlie2 Y hY) hb) (sInCC_mono le_rfl (by simp only [List.length_map]; omega) hF)
    obtain ⟨cF, hcF⟩ := hF
    have hFk : CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) F := hcF.1
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (ap T.coefAdj F') with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hc₁ : ContinuousOn f₁ (GV k r) := CkOn_cont subset_rfl hK₁.1
    have hc₂ : ContinuousOn f₂ (GV k r) := by
      apply CkOn_cont subset_rfl
      rw [hf₂, ← Dw_wR, rho_eq_trn]
      apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hlie2 x (by simpa [wL] using hx))
      apply CkOn_trn _ ha hb
      refine sCkOn_mono ?_ hFk
      simp only [wR, List.length_map, zero_add]
      exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)
    have hb₂ : ∀ g ∈ GV k r, ‖f₂ g‖ ≤ ‖Lp D p‖ * K₂ := by
      intro g hg
      rw [hf₂, rho_eq_trn, Rw_trn _ ha hb _ hlie2
        (sCkOn_mono (by exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)) hFk) g hg]
      exact ((Lp D p).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (CC_bdd hAd0 hK₂ _ (gv_mul (gv_mul ha hg) hb)) (norm_nonneg _))
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hc₂.norm).smul hc₁
    have hGm := aesm_of_continuousOn D hGc
    have hfin := hCC G (‖Lp D p‖ * K₂ * K₁) hGm (by
      intro g hg
      have h1 : gN g ^ A * ‖f₁ g‖ ≤ K₁ := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      have h0 : 0 ≤ gN g ^ A * ‖f₁ g‖ := mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)
      calc gN g ^ A * ‖G g‖ = ‖f₂ g‖ * (gN g ^ A * ‖f₁ g‖) := by rw [hGn]; ring
        _ ≤ ‖Lp D p‖ * K₂ * K₁ := mul_le_mul (hb₂ g hg) h1 h0 ((norm_nonneg _).trans (hb₂ g hg)))
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := ⟨hGm, hfin⟩
    refine hint.norm.congr (Filter.Eventually.of_forall fun g => ?_)
    exact hGn _

theorem gv_stable (D : RealPlaceData k r Wp Wq) : IsStableOpen D (GV k r) :=
  ⟨⟨Set.univ, isOpen_univ, (Set.univ_inter _).symm⟩,
    fun _ hs _ hs' _ hg => gv_mul (gv_mul (Sset_sub hs) hg) (Sset_sub hs')⟩

theorem suppIn_gv (F : Mat k r → (Wq →L[ℂ] Wp)) : SuppIn (GV k r) F :=
  closure_minimal (by exact fun _ hg => hg.1) gv_closed

end GlobalTheory.BetaSym

namespace GlobalTheory

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP.ER BetaSym
open scoped ComplexConjugate

theorem beta_capelli_symm_of_xiExists (hXi : B.XiExists) : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y A : ℝ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → (B.CkOn ⊤ (B.GV k r) (F) ∧ ∀ m : ℕ, B.InCC (A) m (F)) → (B.CkOn ⊤ (B.GV k r) (F') ∧ ∀ m : ℕ, B.InCC (A) m (F')) → B.beta D (Q.CV k r (Y : ℂ) F) F' = B.beta D F (Q.CV k r (Y : ℂ) F') := by
  intro k r Wp Wq _ _ _ _ _ _ D Y A F F' hAB hF hF'
  have hA : 0 ≤ A := le_trans (by unfold B.AB; positivity) hAB
  have hAdj : CapAdj := capAdj_of_int (capAdjInt_of_scalar capacity_adjoint_scalar)
  set Θ := capTh k r Wp Wq 1 (Y : ℂ) with hΘ
  obtain ⟨hord, -, -, -, hApp⟩ := capacity_theta_facts k r Wp Wq D 1 (Y : ℂ) 1 0
  obtain ⟨_, _, _, _, _, h3, _⟩ := BXiAsm.any_of hXi k r Wp Wq D A hAB
  have hS : B.SmoothCoef (B.GV k r) Θ := by
    intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp 1 _ hT
    exact ⟨ckOn_const' _, ckOn_const' _⟩
  have hCo : B.Commutes D (B.GV k r) Θ := by
    intro p hp f hf g hgG
    rw [hΘ, hord] at hf
    have hs' := B7.sgs_mem D hp hgG
    rw [hApp _ (B5.ckOn_rho D hp hf) g hgG, capelli_rho_commute k r Wp Wq D (Y : ℂ) f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  have hP : ∀ T ∈ Θ, ∃ C : ℝ, ∀ (u v : List (B.Mat k r)) (g : B.Mat k r),
      ‖B.dLR u v T.coef g‖ ≤ C ∧ ‖B.dLR u v T.coefAdj g‖ ≤ C := by
    intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp 1 _ hT
    refine ⟨‖c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ + ‖conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖,
      fun u v g => ?_⟩
    have h1 := norm_dLR_const_le (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have h2 := norm_dLR_const_le (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have n1 := norm_nonneg (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    have n2 := norm_nonneg (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    exact ⟨by simp only [TLB.cTerm]; linarith, by simp only [TLB.cTerm]; linarith⟩
  obtain ⟨c1, c2, c3⟩ := clause_bdd D hA (matrix_coefficient_integrable_all k r Wp Wq D A hAB) Θ hS hP F F' (hF.2 _) (hF'.2 _)
  have h1 := h3 (B.GV k r) Θ (gv_stable D) hS hCo F F' (B5.ckOn_mono le_top hF.1) (B5.ckOn_mono le_top hF'.1)
    (suppIn_gv F) (suppIn_gv F') (hF.2 _) (hF'.2 _) c1 c2 c3
  have h0 : B.beta D (Q.CV k r (Y : ℂ) F) F' = B.beta D (B.opApply Θ F) F' :=
    beta_form_congr_holds k r Wp Wq D _ _ _ _
      (fun g hg => by rw [hApp F (B5.ckOn_mono le_top hF.1) g hg, one_smul]) (fun _ _ => rfl)
  have h2 : B.beta D F (B.opAdj Θ F') = B.beta D F (Q.CV k r (Y : ℂ) F') :=
    beta_form_congr_holds k r Wp Wq D _ _ _ _ (fun _ _ => rfl) (fun g hg => by
      rw [hΘ, hAdj k r Wp Wq 1 (Y : ℂ) F' hF'.1 g hg, map_one, Complex.conj_ofReal, one_smul])
  rw [h0, h1, h2]

theorem beta_capelli_symm_of_bessel : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y A : ℝ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → (B.CkOn ⊤ (B.GV k r) (F) ∧ ∀ m : ℕ, B.InCC (A) m (F)) → (B.CkOn ⊤ (B.GV k r) (F') ∧ ∀ m : ℕ, B.InCC (A) m (F')) → B.beta D (Q.CV k r (Y : ℂ) F) F' = B.beta D F (Q.CV k r (Y : ℂ) F') :=
  fun h => beta_capelli_symm_of_xiExists (GlobalTheory.HCXi.xiExists_of_besselXiIntegrable h)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FoldrCapelliSumEigen
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

section
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothLev_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) :
    Q.SmoothLev k r 0 Set.univ (fun y => ∑ i ∈ t, c i • f i y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Formalism.FourierDecayAlt.P.Qx2.smooth_zero
  | insert a t ha ih =>
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', he⟩ := ih g₀ hg₀
    obtain ⟨V, h', hV, hgV, hh', he'⟩ := hf a g₀ hg₀
    refine ⟨U ∩ V, fun y => c a • h' y + f' y, hU.inter hV, ⟨hgU, hgV⟩,
      ((hh'.mono Set.inter_subset_right).const_smul (c a)).add (hf'.mono Set.inter_subset_left), ?_⟩
    intro g hg hgG
    beta_reduce
    rw [Finset.sum_insert ha, he' g hg.2 hgG, ← he g hg.1 hgG]

theorem capelli_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) (Y : ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Q.CV k r Y (fun y => ∑ i ∈ t, c i • f i y) g = ∑ i ∈ t, c i • Q.CV k r Y (f i) g := by
  classical
  have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := E) Y
  have hg' := Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg
  induction t using Finset.induction_on with
  | empty => simpa using hT.map_zero hg'
  | insert a t ha ih =>
    have h := hT.lin _ (f a) (c a) (smoothLev_finsum_smul t c f hf) (hf a) g hg'
    simp only [Finset.sum_insert ha]
    rw [← ih, add_comm, ← h]
    congr 1
    funext y
    rw [add_comm]

end

theorem foldr_capelli_sum_eigen : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ev : Fin N₀ → ℝ → ℂ) (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) → (∀ i (Y : ℝ), ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ev i Y • Fi i g) → (∀ g ∈ B.GV k r, F g = ∑ i, Fi i g) → ∀ w : List (Bool × ℝ), ∀ g ∈ B.GV k r, (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) g = ∑ i, (w.map fun a => s * ev i a.2).prod • Fi i g := by
  intro k r Wp Wq _ _ _ _ _ _ N₀ Fi ev s F hs hev hF w
  induction w with
  | nil => intro g hg; simpa using hF g hg
  | cons a w ih =>
    intro g hg
    have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := Wq →L[ℂ] Wp) (a.2 : ℂ)
    have h1 := hT.loc _ _ (fun y hy => ih y hy.1.1) g (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg)
    have h2 := capelli_finsum_smul Finset.univ (fun i => (w.map fun a => s * ev i a.2).prod) Fi
      (fun i => Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck (hs i)) (a.2 : ℂ) hg
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, Pi.smul_apply]
    rw [h1.trans h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i a.2 g hg, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaSelfReNonneg
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset MeasureTheory

namespace GlobalTheory.BetaPos

theorem bcWeight_nonneg' (k r : ℕ) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

theorem beta_self_re_nonneg : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)), 0 ≤ (B.beta D F F).re := by
  intro k r Wp Wq _ _ _ _ _ _ D F
  have hβ : B.beta D F F = ∫ q : (Fin r → ℂ) × ℂ, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q *
      ‖B.hsVec (B.JF D F (bigCell k r q.1 (D.μsec q.2)))‖ ^ 2 : ℝ) : ℂ) := by
    unfold B.beta betaBig
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only []
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hβ, integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun q => mul_nonneg (bcWeight_nonneg' _ _ _ _ _) (sq_nonneg _)

end GlobalTheory.BetaPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GramBlockDiagonalEnergyBound
open Formalism.REAL Finset

namespace GlobalTheory

theorem abs_list_prod_map_le_of_abs_le {α : Type} (L : List α) (f n : α → ℝ)
    (h : ∀ a ∈ L, |f a| ≤ n a) : |(L.map f).prod| ≤ (L.map n).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

theorem sum_weight_blockDiagonal_eq {ι κ : Type} [Fintype ι] [DecidableEq κ] (B : ι → ι → ℂ)
    (k : ι → κ) (hB : ∀ i j, k i ≠ k j → B i j = 0) (f : κ → ℝ) :
    (∑ i, ∑ j, ((f (k i) : ℝ) : ℂ) * B i j).re =
      ∑ t ∈ Finset.univ.image k, f t *
        (∑ i ∈ Finset.univ.filter (fun i => k i = t),
          ∑ j ∈ Finset.univ.filter (fun j => k j = t), B i j).re := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image k) (g := k)
    (fun i _ => Finset.mem_image_of_mem k (Finset.mem_univ i)), Complex.re_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : k i = t := (Finset.mem_filter.mp hi).2
  rw [← Finset.mul_sum, hi', Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · rfl
  · exact hB i j (fun e => h (e ▸ hi'))

theorem gram_blockDiagonal_energy_bound :
    ∀ (ι α : Type) [Fintype ι] (B : ι → ι → ℂ) (c : ι → α → ℝ) (L : List α) (n : α → ℝ), (∀ S : Finset ι, 0 ≤ (∑ i ∈ S, ∑ j ∈ S, B i j).re) → (∀ i j, ∀ a ∈ L, c i a ≠ c j a → B i j = 0) → (∀ i, ∀ a ∈ L, |c i a| ≤ n a) → (∑ i, ∑ j, (((L.map (c i)).prod : ℝ) : ℂ) * B i j).re ≤ (L.map n).prod * (∑ i, ∑ j, B i j).re := by
  intro ι α _ B c L n hpos hzero hbd
  classical
  have hB : ∀ i j, L.map (c i) ≠ L.map (c j) → B i j = 0 := by
    intro i j hij
    by_contra hne
    apply hij
    refine List.map_congr_left (fun a ha => ?_)
    by_contra h
    exact hne (hzero i j a ha h)
  have e1 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB List.prod
  have e2 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at e2
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun t ht => ?_)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
  exact mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (abs_list_prod_map_le_of_abs_le L (c i) n (hbd i))) (hpos _)

end GlobalTheory
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem levelZero_energy_le_of_eigen_sum :
    GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (s : ℂ) (nn : ℝ → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (s = 1 ∨ s = -1) → B.AB k r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w : List (Bool × ℝ), (C7.principalHermitianLattice D s w F).re ≤ (w.map fun l => nn l.2).prod * (B.beta D F F).re := by
  intro hXi k r Wp Wq _ _ _ _ _ _ D lam d A s nn F hs hA hex hnn w
  obtain ⟨N₀, Fi, ν, hν, hcl, hev, hF⟩ := hex
  obtain ⟨σ, hσs, hσ⟩ : ∃ σ : ℝ, s = (σ : ℂ) ∧ |σ| = 1 := by
    rcases hs with h | h
    · exact ⟨1, by simp [h], by simp⟩
    · exact ⟨-1, by simp [h], by simp⟩
  have h5 : ∀ i, B.InCC A 5 (Fi i) := fun i => (hcl i).2 5
  set e : Fin N₀ → ℝ → ℝ := fun i Y => ∏ t, (Y + lam t + (ν i t : ℝ)) with he
  set c : Fin N₀ → Bool × ℝ → ℝ := fun i a => σ * e i a.2 with hc
  have hF1 : ∀ g ∈ B.GV k r, F g = ∑ i ∈ Finset.univ, (1 : ℂ) • Fi i g := by
    intro g hg; simpa using hF g hg
  have hfold := GlobalTheory.foldr_capelli_sum_eigen k r Wp Wq N₀ Fi (fun i Y => ((e i Y : ℝ) : ℂ)) s F (fun i => (hcl i).1)
    (fun i Y g hg => hev i Y g hg) hF w
  have e1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ _ (fun _ => 1) Fi _ F hA h5 hfold hF1
  have e2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ (fun _ => 1) (fun _ => 1) Fi F F hA h5
    hF1 hF1
  have hcast : ∀ i, (w.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((w.map (c i)).prod : ℝ) : ℂ) := by
    intro i
    have : ∀ v : List (Bool × ℝ),
        (v.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((v.map (c i)).prod : ℝ) : ℂ) := by
      intro v
      induction v with
      | nil => simp
      | cons a v ih =>
        rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, hσs]
        simp only [hc, Complex.ofReal_mul]
    exact this w
  have key := gram_blockDiagonal_energy_bound (Fin N₀) (Bool × ℝ) (fun i j => B.beta D (Fi i) (Fi j)) c w
    (fun l => nn l.2) ?_ ?_ ?_
  · unfold C7.principalHermitianLattice
    rw [e1, e2]
    simp only [star_one, mul_one, one_mul, hcast]
    exact key
  · intro S
    have e3 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) S S (fun _ => 1) (fun _ => 1) Fi
      (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) hA h5
      (fun _ _ => rfl) (fun _ _ => rfl)
    have e4 := GlobalTheory.BetaPos.beta_self_re_nonneg k r Wp Wq D (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g)
    rw [e3] at e4
    simpa only [star_one, mul_one, one_mul] using e4
  · intro i j a _ hne
    have hne' : e i a.2 ≠ e j a.2 := fun h => hne (by simp only [hc, h])
    have hsym := GlobalTheory.beta_capelli_symm_of_bessel hXi k r Wp Wq D a.2 A (Fi i) (Fi j) hA (hcl i) (hcl j)
    have h1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => ((e i a.2 : ℝ) : ℂ)) (fun _ => 1) Fi (Q.CV k r (a.2 : ℂ) (Fi i)) (Fi j) hA h5
      (fun g hg => by rw [Finset.sum_singleton]; exact hev i a.2 g hg) (fun g _ => by simp)
    have h2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => 1) (fun _ => ((e j a.2 : ℝ) : ℂ)) Fi (Fi i) (Q.CV k r (a.2 : ℂ) (Fi j)) hA h5
      (fun g _ => by simp) (fun g hg => by rw [Finset.sum_singleton]; exact hev j a.2 g hg)
    simp only [Finset.sum_singleton, star_one, mul_one, one_mul,
      Complex.star_def, Complex.conj_ofReal] at h1 h2
    rw [h1, h2] at hsym
    have hcc : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne')
    have h0 : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) * B.beta D (Fi i) (Fi j) = 0 := by
      rw [sub_mul, hsym, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hcc
  · intro i a _
    refine le_trans ?_ (hnn a.2)
    simp only [hc, he, abs_mul, hσ, one_mul, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun t _ => (abs_add_le _ _).trans ?_)
    have : |(ν i t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν i t
    linarith

end GlobalTheory
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

open scoped Matrix.Norms.Elementwise in
theorem ckOn_group_finset_sum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type}
    (s : Finset ι) (Fi : ι → B.Mat k r → E) (h : ∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) :
    B.CkOn ⊤ (B.GV k r) (fun g => ∑ i ∈ s, Fi i g) := by
  intro g₀ hg₀
  choose U f hU hgU hf hff using fun i => h i g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun g => ∑ i ∈ s, f i g, isOpen_biInter_finset fun i _ => hU i,
    Set.mem_iInter₂.2 fun i _ => hgU i, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi => (hf i).mono fun g hg => Set.mem_iInter₂.1 hg i hi
  · intro g hg hG
    exact Finset.sum_congr rfl fun i hi => hff i g (Set.mem_iInter₂.1 hg i hi) hG

theorem levelZero_form_le_normC_of_eigen_sum : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (d : ℕ) (A : ℝ) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.AB P.k P.r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * P.r + P.k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV P.k P.r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV P.k P.r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR F 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re := by
  intro hXi Wp Wq _ _ _ _ _ _ P p lam d A nn F Y N hA hF hnn w hw _
  have hsm : B.CkOn ⊤ (B.GV P.k P.r) F := by
    obtain ⟨N₀, Fi, ν, -, hc, -, hsum⟩ := hF
    exact (ckOn_inCC_congr_on_group P.k P.r _ A (fun g => ∑ i, Fi i g) F
      (fun g hg => (hsum g hg).symm)).1 (ckOn_group_finset_sum Finset.univ Fi fun i => (hc i).1)
  have hs : M.sgn P p.l0 = 1 ∨ M.sgn P p.l0 = -1 := by
    unfold M.sgn
    exact neg_one_pow_eq_or ℂ _
  unfold KB.Pl.RR TBB.normC
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hsm (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw.1)]
  exact GlobalTheory.levelZero_energy_le_of_eigen_sum hXi P.k P.r Wp Wq p.T.base lam d A _ nn F hs hA hF hnn w

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EnergyBoundPolynomialWeightPowCapelliEigen
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem energy_bound_gfPow_smul_comp_polyOp : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wf : Type) [NormedAddCommGroup Wf] [InnerProductSpace ℂ Wf] [FiniteDimensional ℂ Wf] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wf →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq →L[ℂ] Wf)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq →L[ℂ] Wf)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g))).re := by
  intro hXi Wp Wq _ _ _ _ _ _ Wf _ _ _ P p lam lam' cs A₀ p₀ dA nn f Aop Y N hA hC hI hE hgap hcl hAB hnn
    w hw hN
  have hgap' : ∀ s t, s ≠ t →
      2 * (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) < |lam' s - lam' t| := by
    intro s t hst
    have h1 := hgap s t hst
    have h2 := hcl s
    have h3 := hcl t
    have h4 : |lam s - lam t| ≤ |lam' s - lam' t| + |lam' s - lam s| + |lam' t - lam t| := by
      have e : lam s - lam t = (lam' s - lam' t) - (lam' s - lam s) + (lam' t - lam t) := by ring
      rw [e]
      have a1 := abs_add_le ((lam' s - lam' t) - (lam' s - lam s)) (lam' t - lam t)
      have a2 := abs_sub (lam' s - lam' t) (lam' s - lam s)
      linarith
    linarith
  have hes := GlobalTheory.T.capelliEigenfunction_pow_smul_comp_polyFamily_eigenSum P.k P.r Wp Wf Wq p.T.base.z p.T.base.z' lam' A₀ p₀ dA f Aop hgap'
    ⟨hC, hI⟩ hE hA
  refine GlobalTheory.levelZero_form_le_normC_of_eigen_sum hXi Wp Wq P p lam' ((2 * P.r + 2) * p₀ + dA) _ nn _ Y N hAB hes ?_ w hw hN
  intro y
  refine le_trans (Finset.prod_le_prod₀ (fun s _ => by positivity) (fun s _ => ?_)) (hnn y)
  have h2 := hcl s
  have e : y + lam' s = (y + lam s) + (lam' s - lam s) := by ring
  have a1 := abs_add_le (y + lam s) (lam' s - lam s)
  rw [e]
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EnergyBoundPolynomialWeightPowCapelliEigenStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wf : Type) [NormedAddCommGroup Wf] [InnerProductSpace ℂ Wf] [FiniteDimensional ℂ Wf] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wf →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq →L[ℂ] Wf)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq →L[ℂ] Wf)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g))).re := by
  first | exact @GlobalTheory.energy_bound_gfPow_smul_comp_polyOp | exact GlobalTheory.energy_bound_gfPow_smul_comp_polyOp | (intros; apply GlobalTheory.energy_bound_gfPow_smul_comp_polyOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyBoundDecayingCasimirEigenfunction
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem limBd_fpm_and_fpmSh : GlobalTheory.HCXi.BesselXiIntegrable → (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd p nn (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N) ∧ (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (P : M.Par) (u u' : ℕ → ℝ) (q : KB.Pl (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') Wp Wq') (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd q nn (Formalism.FourierDecayAlt.P.CutBP2.fpmSh q f Aop p₀) Y N) := by
  intro hXi
  refine ⟨?_, ?_⟩
  · intro Wp Wq _ _ _ _ _ _ P p lam lam' cs A₀ p₀ nn f Y N h1 h2 h3 h4 h5 h6 h7
    refine GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen hXi Wp Wq Wq P p lam lam' cs A₀ p₀ 0 nn f
      (fun _ => ContinuousLinearMap.id ℂ Wq) Y N ?_ h1 h2 h3 h4 h5 h6 h7
    refine ⟨1, fun _ _ => 1, fun _ => ContinuousLinearMap.id ℂ Wq, fun _ => ?_, fun g => by simp⟩
    exact ⟨1, by simp, fun g => by simp⟩
  · intro Wp Wq _ _ _ _ _ _ Wq' _ _ _ P u u' q lam lam' cs A₀ p₀ dA nn f Aop Y N h0 h1 h2 h3 h4 h5 h6 h7
    exact GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen hXi Wp Wq' Wq (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') q lam lam' cs A₀ p₀ dA nn f Aop Y N
      h0 h1 h2 h3 h4 h5 h6 h7

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyBoundDecayingCasimirEigenfunctionStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroEnergyBound_decayingCasimirEigenfunction : GlobalTheory.HCXi.BesselXiIntegrable → (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd p nn (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N) ∧ (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (P : M.Par) (u u' : ℕ → ℝ) (q : KB.Pl (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') Wp Wq') (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd q nn (Formalism.FourierDecayAlt.P.CutBP2.fpmSh q f Aop p₀) Y N) := by
  first | exact @GlobalTheory.limBd_fpm_and_fpmSh | exact GlobalTheory.limBd_fpm_and_fpmSh | (intros; apply GlobalTheory.limBd_fpm_and_fpmSh <;> assumption)
end
