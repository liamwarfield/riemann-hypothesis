module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertPrime
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertIncrement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsVeryAmpleZFinite

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

noncomputable def baseComap (F : Type) [Field F] {K : Type} {ι : K → Type} (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (W : Ideal (NumbersDVR.MRing ι F)) : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F) :=
  W.comap (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k))

def ModelCurves.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ d : ℕ,
        (∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
          relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) →
            NumbersDVR.IsMultiProjPrime (baseComap F k₀ e W) ∧
              mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ baseComap F k₀ e W ∧
              relDim (baseComap F k₀ e W) = ((d : ℕ) : WithBot (WithTop ℤ))) ∧
        (∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F), NumbersDVR.IsMultiProjPrime P →
          mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ P → relDim P = ((d : ℕ) : WithBot (WithTop ℤ)) →
            ∃ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W ∧ mIdealOver F y ≤ W ∧
              relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) ∧ baseComap F k₀ e W = P)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def segreJoin {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) :
    (Σ k, Sum.elim (fun _ : Unit => ∀ k, ι k) ι k) → Ω :=
  IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (NumbersDVR.segreVec y)) y

def SegreBase.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S (segreJoin y) (Sum.inl ()) ∧
      (∀ β : K → ℤ, secOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) = secOver S y β) ∧
      ∀ (β : K → ℤ) (n : ℕ) (η : Fin n → Ω),
        GeneratesOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) η ↔ GeneratesOver S y β η

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace HilbertPositive

theorem hilbertPrime : HilbertSamuel.HilbertPrime.Statement.{u} :=
  HilbertSamuel.HilbertPrime.proof HilbertSamuel.HilbertDimZero.proof
    (HilbertSamuel.HilbertIncrement.proof HilbertSamuel.IntersectionRecursion.proof)
    (HilbertSamuel.MixedNumberPolynomial.proof
      (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof))
    (HilbertSamuel.ModulesFromPrimes.proof HilbertSamuel.MultigradedFiltration.proof
      HilbertSamuel.FiltrationHilbSum.proof HilbertSamuel.DegLTGrowth.proof)

theorem mixedNumber : HilbertSamuel.MixedNumberPolynomial.Statement.{u} :=
  HilbertSamuel.MixedNumberPolynomial.proof
    (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof)

def blockEquiv (N : ℕ) : (Σ _ : Unit, Fin (N + 1)) ≃ Fin (N + 1) where
  toFun v := v.2
  invFun i := ⟨(), i⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem weight_blockWeight_one (d : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) d = fun _ => d.degree := by
  funext u
  rw [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [NumbersDVR.blockWeight]

theorem isWeightedHomogeneous_iff (p : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) p (fun _ => n) ↔
      p.IsHomogeneous n := by
  constructor
  · intro h d hd
    have h1 : d.degree = n := congrFun ((weight_blockWeight_one d).symm.trans (h hd)) ()
    rw [← h1, Finsupp.degree_eq_weight_one]
    rfl
  · intro h d hd
    rw [weight_blockWeight_one]
    funext _
    rw [Finsupp.degree_eq_weight_one]
    exact h hd

theorem ringKrullDim_primeOfOne (y : Fin (N + 1) → Ω) :
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ringKrullDim (Poly k N ⧸ primeOf (S := k) y) := by
  let f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (blockEquiv N)).toRingEquiv
  have hc : primeOfOne (S := k) y = (primeOf (S := k) y).comap f.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  have h : primeOf (S := k) y = (primeOfOne (S := k) y).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

theorem ne_zero_of_isSubvar {y : Fin (N + 1) → Ω} {e : ℕ} (h : IsSubvar y (primeOf (S := k) y) e) :
    y ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  intro hy
  apply hi
  rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k i), aeval_X, hy, Pi.zero_apply]

theorem finrank_piece_eq_hilbFn (y : Fin (N + 1) → Ω) (n : ℕ) :
    (Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ) =
      NumbersDVR.hilbFn (primeOfOne (S := k) y) (fun _ => (n : ℤ)) := by
  classical
  rw [NumbersDVR.hilbFn, if_pos (fun _ => Int.natCast_nonneg n)]
  simp only [Int.toNat_natCast]
  congr 1
  set V := weightedHomogeneousSubmodule k (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1)))
    (fun _ : Unit => n) with hV
  let f₁ : V →ₗ[k] NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y :=
    (Ideal.Quotient.mkₐ k (primeOfOne (S := k) y)).toLinearMap ∘ₗ V.subtype
  let f₂ : V →ₗ[k] Ω :=
    (aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2)).toLinearMap ∘ₗ V.subtype
  have hhom : ∀ v ∈ V, (oneBlock (S := k) (N := N) v).IsHomogeneous n := fun v hv =>
    ((isWeightedHomogeneous_iff v n).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hv)).rename_isHomogeneous
  have heval : ∀ v, aeval y (oneBlock (S := k) (N := N) v) = aeval (fun w : Σ _ : Unit, Fin (N + 1) => y w.2) v :=
    fun v => by rw [oneBlock, aeval_rename]; rfl
  have hr₁ : LinearMap.range f₁ = NumbersDVR.gradedPiece (primeOfOne (S := k) y) (fun _ => n) := by
    rw [NumbersDVR.gradedPiece, LinearMap.range_comp, Submodule.range_subtype]
  have hr₂ : LinearMap.range f₂ = (coordGraded k y).piece (n : ℤ) := by
    apply le_antisymm
    · rintro _ ⟨⟨v, hv⟩, rfl⟩
      refine Submodule.subset_span ⟨oneBlock (S := k) (N := N) v, n, hhom v hv, rfl, ?_⟩
      exact (heval v).symm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, e, hg, he, rfl⟩
      have he' : e = n := by exact_mod_cast he
      subst he'
      refine ⟨⟨rename (blockEquiv N).symm g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        ((isWeightedHomogeneous_iff _ e).mpr (hg.rename_isHomogeneous))⟩, ?_⟩
      change aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2) (rename (blockEquiv N).symm g) = aeval y g
      rw [aeval_rename]
      rfl
  have hker : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    ext ⟨v, hv⟩
    simp only [LinearMap.mem_ker, f₁, f₂, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    change oneBlock (S := k) (N := N) v ∈ primeOf (S := k) y ↔ _
    rw [mem_primeOf_of_isHomogeneous y (hhom v hv), heval]
  have e₁ := ((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
    f₂.quotKerEquivRange).finrank_eq
  rw [hr₁, hr₂] at e₁
  exact e₁.symm

end HilbertPositive


open HilbertPositive in
theorem HilbertPositive.proof (hPos : ProjDegreePositive.Statement.{u})
    (hSec : TwistSections.Statement.{u, w}) : HilbertPositive.Statement.{u, w} := by
  intro k _ Ω _ _ N y e he hW
  have hy : y ≠ 0 := ne_zero_of_isSubvar hW
  have hq : NumbersDVR.IsMultiProjPrime (primeOfOne (S := k) y) := isMultiProjPrime_primeOfOne y hy
  have hdim : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_primeOfOne]
    exact hW.dim
  refine ⟨?_, hPos k (Fin (N + 1)) _ e hq hdim, hSec k Ω N y hy⟩
  have hdim' : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    simpa using hdim
  obtain ⟨a₀, C, hC⟩ := hilbertPrime e k Unit (fun _ => Fin (N + 1)) _ hq hdim'
  have hadd := (mixedNumber k Unit (fun _ => Fin (N + 1)) _ e hq hdim').2
  have hhom : ∀ n : ℕ, NumbersDVR.intNum k (primeOfOne (S := k) y)
      (fun _ : Fin e => fun _ : Unit => (n : ℤ)) = (n : ℤ) ^ e *
        NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) := by
    intro n
    have := HilbertSamuel.RankOfSections.const_nsmul
      (fun bs => NumbersDVR.intNum k (primeOfOne (S := k) y) bs) hadd n (fun _ : Unit => (1 : ℤ))
    have e' : (n • fun _ : Unit => (1 : ℤ)) = fun _ : Unit => (n : ℤ) := by
      funext u
      simp
    rw [e'] at this
    exact this
  refine ⟨|C| * 2 ^ (e - 1), ?_⟩
  filter_upwards [eventually_ge_atTop (max a₀ 1)] with n hn
  have h := hC (fun _ => n) (fun _ => le_of_max_le_left hn)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [hhom n, ← finrank_piece_eq_hilbFn] at h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpow : ((n : ℝ) + 1) ^ ((e : ℝ) - 1) ≤ 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by
    rw [show (e : ℝ) - 1 = ((e - 1 : ℕ) : ℝ) by rw [Nat.cast_sub he]; simp, Real.rpow_natCast,
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc |(Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℝ) -
        (NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℝ) *
          (n : ℝ) ^ e / (e.factorial : ℝ)|
      = |(((Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ)) : ℝ) -
          (((n : ℤ) ^ e * NumbersDVR.intNum k (primeOfOne (S := k) y)
            (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℤ) : ℝ) / (e.factorial : ℝ)| := by
        push_cast
        ring_nf
    _ ≤ C * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) := h
    _ ≤ |C| * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (e - 1) * (n : ℝ) ^ (e - 1)) := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = |C| * 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutZeroNotLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section CutZeroNotLeAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_zeroIdeal_div_eq (D : SubFamily S x Ω) (hfg : ∀ K, (D.sub K).FG) (I : Chart x)
    {σ y : Ω} (hσ : σ ∈ D.sub I) (hy : ∀ δ ∈ D.sub I, y * δ ∈ chartRing S x I) :
    ∃ (g t : Poly S N) (n : ℕ), g ∈ zeroIdeal D.toSubSystem σ ∧ t ∈ monos I.1 ∧
      g.IsHomogeneous n ∧ t.IsHomogeneous n ∧ σ * y = aeval x g / aeval x t := by
  classical

  obtain ⟨f, s, n, hs, hf, hsn, hz⟩ := hy σ hσ
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hfz : y * σ * aeval x s = aeval x f := (eq_div_iff hs0).mp hz

  have hyU := mul_mem_chartRing_union D I
  choose G hG using hfg
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1) := fun p =>
    hyU p.1 y hy _ (D.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)

  obtain ⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := S) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  have hUK : ∀ (K : Chart x), ∀ δ ∈ D.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by
    intro K δ hδ
    rw [← hG K] at hδ
    induction hδ using Submodule.span_induction with
    | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
    | smul a b _ hb =>
      rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
        ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hb
  have hU0 := eval_ne_zero_of_mem_monos I hUm

  have hfU : f * U ∈ zeroIdeal D.toSubSystem σ := by
    refine Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ hδ)
    · rw [map_mul, ← hfz]
      ring
  refine ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩
  rw [map_mul, map_mul, ← hfz]
  field_simp

end CutZeroNotLeAux

theorem CutZeroNotLe.proof : CutZeroNotLe.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp L s _ hs ⟨I, hI⟩
  have hsI : s ∈ L.sub I := (Submodule.mem_iInf _).mp hs I
  obtain ⟨P, hP⟩ := L.invertible I

  have hex : ∃ y ∈ P, s * y ∉ idealMod pp I := by
    by_contra hcon
    push Not at hcon
    apply hI
    rw [SubSystem.twist_sub_eq_mul_sub]
    have hle : Submodule.span (chartRing k x I) {s} * P ≤ idealMod pp I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c (hcon b hb)
    have hmem : s ∈ Submodule.span (chartRing k x I) {s} * P * L.sub I := by
      rw [mul_assoc, mul_comm P, hP, mul_one]
      exact Submodule.mem_span_singleton_self s
    exact mul_le_mul' hle le_rfl hmem
  obtain ⟨y, hyP, hsy⟩ := hex
  have hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing k x I := by
    intro δ hδ
    have h := Submodule.mul_mem_mul hδ hyP
    rw [hP] at h
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp h
    rw [mul_comm, ← ha]
    exact a.2
  obtain ⟨g, t, n, hg, ht, hgn, htn, hst⟩ := exists_zeroIdeal_div_eq L.toSubFamily L.fg I hsI hy
  refine ⟨g, hg, fun hgp => hsy ?_⟩
  rw [hst]
  exact Submodule.subset_span ⟨g, t, n, hgp, ht, hgn, htn, rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoeNeZeroOfNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn)

noncomputable section

section ResidueMap

variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω] {K : Type} {ι : K → Type}
  (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [hp : p.IsPrime]

open IndefiniteRowSideFullHecke.Kleiman2 (ResField)

instance resField.isFractionRing : IsFractionRing (chartRingOver S y c ⧸ p) (ResField S y c p) :=
  inferInstanceAs (IsFractionRing (chartRingOver S y c ⧸ p) (FractionRing (chartRingOver S y c ⧸ p)))

omit hp in
theorem coe_ne_zero_of_notMem {b : (chartRingOver S y c)} (hb : b ∉ p) : (b : Ω) ≠ 0 := by
  intro h
  apply hb
  have : b = 0 := Subtype.ext h
  rw [this]
  exact p.zero_mem

theorem mem_locIn_chart_iff {u : Ω} : u ∈ locIn (chartRingOver S y c) p ↔ ∃ a b : (chartRingOver S y c), b ∉ p ∧ u = (a : Ω) / b := by
  constructor
  · intro hu
    induction hu using Subring.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, 1, Ideal.one_notMem p, by simp⟩
    | one => exact ⟨1, 1, Ideal.one_notMem p, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      obtain ⟨a', b', hb', rfl⟩ := hy
      refine ⟨a * b' + b * a', b * b', hp.mul_notMem hb hb', ?_⟩
      rw [div_add_div _ _ (coe_ne_zero_of_notMem y c p hb) (coe_ne_zero_of_notMem y c p hb')]
      simp
    | neg x _ hx =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      exact ⟨-a, b, hb, by simp [neg_div]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      obtain ⟨a', b', hb', rfl⟩ := hy
      exact ⟨a * a', b * b', hp.mul_notMem hb hb', by simp [div_mul_div_comm]⟩
  · intro h
    exact Subring.subset_closure h

def resq (a : (chartRingOver S y c)) : ResField S y c p :=
  algebraMap (chartRingOver S y c ⧸ p) (ResField S y c p) (Ideal.Quotient.mk p a)

theorem resq_eq_zero_iff (a : (chartRingOver S y c)) : resq y c p a = 0 ↔ a ∈ p := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, resq]
  constructor
  · intro h
    exact IsFractionRing.injective (chartRingOver S y c ⧸ p) (ResField S y c p) (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

theorem resq_ne_zero {b : (chartRingOver S y c)} (hb : b ∉ p) : resq y c p b ≠ 0 :=
  fun h => hb ((resq_eq_zero_iff y c p b).mp h)

theorem resq_mul (a b : (chartRingOver S y c)) : resq y c p (a * b) = resq y c p a * resq y c p b := by
  simp [resq, map_mul]

theorem resq_add (a b : (chartRingOver S y c)) : resq y c p (a + b) = resq y c p a + resq y c p b := by
  simp only [resq, RingHom.map_add]

theorem resq_div_eq {a b a' b' : (chartRingOver S y c)} (hb : b ∉ p) (hb' : b' ∉ p) (h : (a : Ω) / b = (a' : Ω) / b') :
    resq y c p a / resq y c p b = resq y c p a' / resq y c p b' := by
  rw [div_eq_div_iff (coe_ne_zero_of_notMem y c p hb) (coe_ne_zero_of_notMem y c p hb')] at h
  have h' : a * b' = a' * b := Subtype.ext (by simpa using h)
  rw [div_eq_div_iff (resq_ne_zero y c p hb) (resq_ne_zero y c p hb'), ← resq_mul, ← resq_mul, h']

theorem exists_rep (u : locIn (chartRingOver S y c) p) : ∃ a b : (chartRingOver S y c), b ∉ p ∧ (u : Ω) = (a : Ω) / b :=
  (mem_locIn_chart_iff y c p).mp u.2

def resFun (u : locIn (chartRingOver S y c) p) : ResField S y c p :=
  resq y c p (exists_rep y c p u).choose / resq y c p (exists_rep y c p u).choose_spec.choose

theorem resFun_eq (u : locIn (chartRingOver S y c) p) {a b : (chartRingOver S y c)} (hb : b ∉ p) (hu : (u : Ω) = a / b) :
    resFun y c p u = resq y c p a / resq y c p b := by
  obtain ⟨hb0, hu0⟩ := (exists_rep y c p u).choose_spec.choose_spec
  exact resq_div_eq y c p hb0 hb (hu0.symm.trans hu)

def resMap : locIn (chartRingOver S y c) p →+* ResField S y c p where
  toFun := resFun y c p
  map_one' := by
    rw [resFun_eq y c p 1 (a := 1) (b := 1) (Ideal.one_notMem p) (by simp)]
    simp [resq]
  map_mul' u v := by
    obtain ⟨a, b, hb, hu⟩ := exists_rep y c p u
    obtain ⟨a', b', hb', hv⟩ := exists_rep y c p v
    rw [resFun_eq y c p u hb hu, resFun_eq y c p v hb' hv,
      resFun_eq y c p (u * v) (a := a * a') (b := b * b') (hp.mul_notMem hb hb')
        (by simp [hu, hv, div_mul_div_comm]), resq_mul, resq_mul, div_mul_div_comm]
  map_zero' := by
    rw [resFun_eq y c p 0 (a := 0) (b := 1) (Ideal.one_notMem p) (by simp)]
    simp [resq]
  map_add' u v := by
    obtain ⟨a, b, hb, hu⟩ := exists_rep y c p u
    obtain ⟨a', b', hb', hv⟩ := exists_rep y c p v
    rw [resFun_eq y c p u hb hu, resFun_eq y c p v hb' hv,
      resFun_eq y c p (u + v) (a := a * b' + b * a') (b := b * b') (hp.mul_notMem hb hb') (by
        rw [Subring.coe_add, hu, hv,
          div_add_div _ _ (coe_ne_zero_of_notMem y c p hb) (coe_ne_zero_of_notMem y c p hb')]
        simp),
      div_add_div _ _ (resq_ne_zero y c p hb) (resq_ne_zero y c p hb'), resq_add, resq_mul, resq_mul, resq_mul]

theorem resMap_eq (u : locIn (chartRingOver S y c) p) {a b : (chartRingOver S y c)} (hb : b ∉ p) (hu : (u : Ω) = a / b) :
    resMap y c p u = resq y c p a / resq y c p b :=
  resFun_eq y c p u hb hu

theorem resMap_of_mem (a : (chartRingOver S y c)) (h : (a : Ω) ∈ locIn (chartRingOver S y c) p) : resMap y c p ⟨a, h⟩ = resq y c p a := by
  rw [resMap_eq y c p _ (a := a) (b := 1) (Ideal.one_notMem p) (by simp)]
  simp [resq]

end ResidueMap

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TrdegEqOfLeOfIsAlgebraic
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)

section Trdeg

variable {F : Type} [Field F] {B : Type} [CommRing B] [IsDomain B] [Algebra F B]

theorem trdeg_eq_of_le_of_isAlgebraic {S T : Subalgebra F B} (hST : S ≤ T)
    (halg : ∀ t ∈ T, IsAlgebraic S t) : Algebra.trdeg F S = Algebra.trdeg F T := by
  let _ : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  have _ : IsScalarTower F S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : FaithfulSMul F S :=
    (faithfulSMul_iff_algebraMap_injective F S).2 (algebraMap F S).injective
  have _ : FaithfulSMul S T :=
    (faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)
  let f : T →ₐ[S] B := { T.val.toRingHom with commutes' := fun _ => rfl }
  have _ : Algebra.IsAlgebraic S T :=
    ⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩
  have h := trdeg_add_eq F S (A := T)
  rw [trdeg_eq_zero (R := S) (A := T), add_zero] at h
  exact h

theorem isAlgebraic_of_mem_adjoin (S : Subalgebra F B) {s : Set B} (hs : ∀ b ∈ s, IsAlgebraic S b)
    {b : B} (hb : b ∈ Algebra.adjoin F s) : IsAlgebraic S b := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r => exact isAlgebraic_algebraMap (⟨algebraMap F B r, S.algebraMap_mem r⟩ : S)
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

theorem trdeg_eq_of_isAlgebraic_both {S T : Subalgebra F B} (h₁ : ∀ t ∈ T, IsAlgebraic S t)
    (h₂ : ∀ s ∈ S, IsAlgebraic T s) : Algebra.trdeg F S = Algebra.trdeg F T := by
  have hS : ∀ b ∈ S ⊔ T, IsAlgebraic S b := fun b hb =>
    isAlgebraic_of_mem_adjoin S (fun b (hb : b ∈ (S : Set B) ∪ T) =>
      Or.elim hb (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : S)) (h₁ b))
      (by rwa [Algebra.sup_def] at hb)
  have hT : ∀ b ∈ S ⊔ T, IsAlgebraic T b := fun b hb =>
    isAlgebraic_of_mem_adjoin T (fun b (hb : b ∈ (S : Set B) ∪ T) =>
      Or.elim hb (h₂ b) (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : T)))
      (by rwa [Algebra.sup_def] at hb)
  rw [trdeg_eq_of_le_of_isAlgebraic le_sup_left hS, trdeg_eq_of_le_of_isAlgebraic le_sup_right hT]

end Trdeg

section LocalRings

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem isAlgebraic_of_mem_locIn (A : Subalgebra F Ω) (p : Ideal A) [p.IsPrime] {u : Ω}
    (hu : u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : IsAlgebraic A u := by
  unfold IndefiniteRowSideFullHecke.Kleiman2.locIn at hu
  induction hu using Subring.closure_induction with
  | mem u hu =>
    obtain ⟨a, b, hb, rfl⟩ := hu
    have hb0 : (b : Ω) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact p.zero_mem)
    refine IsAlgebraic.of_mul (y := (b : Ω)) (mem_nonZeroDivisors_of_ne_zero hb0)
      (isAlgebraic_algebraMap b) ?_
    have e : (b : Ω) * ((a : Ω) / b) = algebraMap A Ω a := by
      rw [mul_div_cancel₀ _ hb0]; rfl
    rw [e]
    exact isAlgebraic_algebraMap a
  | zero => exact isAlgebraic_zero
  | one => exact isAlgebraic_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | mul x y _ _ hx hy => exact hx.mul hy

theorem le_locIn (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨⟨a, ha⟩, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h), by simp⟩

theorem exists_trdeg_chartRing_eq {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel F y y') (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ c' : ∀ k, ι' k, (∀ k, y' ⟨k, c' k⟩ ≠ 0) ∧
      Algebra.trdeg F (chartRingOver F y c) = Algebra.trdeg F (chartRingOver F y' c') := by
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥ ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F y :=
    ⟨c, hc, ⊥, Ideal.isPrime_bot, rfl⟩
  unfold IndefiniteRowSideFullHecke.Kleiman2.SameModel at h
  rw [h] at hz
  obtain ⟨c', hc', p', hp', hzeq⟩ := hz
  refine ⟨c', hc', trdeg_eq_of_isAlgebraic_both (fun t ht => ?_) (fun s hs => ?_)⟩
  · have ht' : t ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥ := by
      rw [hzeq]; exact le_locIn _ p' ht
    exact isAlgebraic_of_mem_locIn _ ⊥ ht'
  · have hs' : s ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y' c') p' := by
      rw [← hzeq]; exact le_locIn _ ⊥ hs
    exact isAlgebraic_of_mem_locIn _ p' hs'

end LocalRings

section Cone

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
variable {K : Type} {ι : K → Type}

def chartConeMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    MvPolynomial K (chartRingOver F y c) →ₐ[F] MvPolynomial K Ω :=
  ((aeval fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars
    F).comp (MvPolynomial.mapAlgHom (chartRingOver F y c).val)

theorem chartConeMap_C (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : chartRingOver F y c) :
    chartConeMap y c (MvPolynomial.C a) = MvPolynomial.C (a : Ω) := by
  simp [chartConeMap]

theorem chartConeMap_X (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    chartConeMap (F := F) y c (X k) = MvPolynomial.C (y ⟨k, c k⟩) * X k := by
  simp [chartConeMap]

theorem mConeMapOver_X (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) :
    mConeMapOver F y (X p) = MvPolynomial.C (y p) * X p.1 := by
  simp [mConeMapOver]

theorem chartConeMap_injective (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Function.Injective (chartConeMap (F := F) y c) := by
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k
  let ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => MvPolynomial.C (y ⟨k, c k⟩)⁻¹ * X k
  have hinv : ψ'.comp ψ = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]
  have hψ : Function.Injective ψ := Function.LeftInverse.injective (g := ψ') fun p => by
    rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  exact hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)

theorem trdeg_quotient_mIdealOver [Fintype K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.trdeg F (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) =
      Algebra.trdeg F (chartRingOver F y c) + Fintype.card K := by
  have hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ chartRingOver F y c := fun p =>
    Algebra.subset_adjoin ⟨p, rfl⟩

  let ρ : MvPolynomial (Σ k, ι k) F →ₐ[F] MvPolynomial K (chartRingOver F y c) :=
    aeval fun p => MvPolynomial.C (⟨_, hu p⟩ : (chartRingOver F y c)) * X p.1
  have hfac : mConeMapOver F y = (chartConeMap (F := F) y c).comp ρ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [mConeMapOver_X, AlgHom.comp_apply]
    rw [aeval_X, map_mul, chartConeMap_C, chartConeMap_X, ← mul_assoc, ← map_mul]
    simp only [div_mul_cancel₀ _ (hc p.1)]
  set R := (mConeMapOver F y).range
  have hle : R ≤ (chartConeMap (F := F) y c).range := by
    show (mConeMapOver F y).range ≤ _
    rw [hfac]; exact AlgHom.range_comp_le_range _ _
  have hUR : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ∈ R := fun k =>
    ⟨X ⟨k, c k⟩, mConeMapOver_X y _⟩
  have hU0 : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ≠ 0 := fun k =>
    mul_ne_zero (MvPolynomial.C_ne_zero.2 (hc k)) (MvPolynomial.X_ne_zero k)

  have halgC : ∀ w ∈ (chartRingOver F y c), IsAlgebraic R (MvPolynomial.C w : MvPolynomial K Ω) := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      refine IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1)
        (mem_nonZeroDivisors_of_ne_zero (hU0 p.1)) (isAlgebraic_algebraMap (⟨_, hUR p.1⟩ : R)) ?_
      have e : (MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1 : MvPolynomial K Ω) *
          MvPolynomial.C (y p / y ⟨p.1, c p.1⟩) = mConeMapOver F y (X p) := by
        rw [mConeMapOver_X, mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hc p.1)]
      rw [e]
      exact isAlgebraic_algebraMap (⟨_, AlgHom.mem_range_self _ _⟩ : R)
    | algebraMap r =>
      exact isAlgebraic_algebraMap (⟨algebraMap F _ r, R.algebraMap_mem r⟩ : R)
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact hx.add hy
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy
  have halg : ∀ t ∈ (chartConeMap (F := F) y c).range, IsAlgebraic R t := by
    rintro _ ⟨q, rfl⟩
    change IsAlgebraic R (chartConeMap (F := F) y c q)
    induction q using MvPolynomial.induction_on with
    | C a => rw [chartConeMap_C]; exact halgC a a.2
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p k hp =>
      rw [map_mul, chartConeMap_X]
      exact hp.mul (isAlgebraic_algebraMap (⟨_, hUR k⟩ : R))
  have h1 : Algebra.trdeg F (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = Algebra.trdeg F R :=
    (Ideal.quotientKerEquivRange (mConeMapOver F y)).trdeg_eq
  have h2 : Algebra.trdeg F (chartConeMap (F := F) y c).range =
      Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) :=
    (AlgEquiv.ofInjective (chartConeMap (F := F) y c) (chartConeMap_injective y c hc)).trdeg_eq.symm
  have _ : FaithfulSMul F (chartRingOver F y c) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F (chartRingOver F y c)).injective
  have _ : FaithfulSMul (chartRingOver F y c) (MvPolynomial K (chartRingOver F y c)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective K _)
  have h3 : Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) =
      Algebra.trdeg F (chartRingOver F y c) + Fintype.card K := by
    rw [← trdeg_add_eq F (chartRingOver F y c) (A := MvPolynomial K (chartRingOver F y c)),
      MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [h1, trdeg_eq_of_le_of_isAlgebraic hle halg, h2, h3]

end Cone

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelDimEq.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ d : ℕ,
      (Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
          (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) d ↔
        relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubFamilyTwistPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem SubFamily.mem_twist_iff (F : SubFamily S x E) (Q : SubFamily S x Ω) (I J : Chart x) (h : I.1 ⊆ J.1)
    (y : E) : y ∈ (F.toSubSystem.twist Q.toSubSystem).sub J ↔
      ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
        (a : Ω) • y ∈ (F.toSubSystem.twist Q.toSubSystem).sub I := by
  constructor
  · intro hy
    refine Submodule.span_induction (p := fun y _ => ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (F.toSubSystem.twist Q.toSubSystem).sub I) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨q, hq, z, hz, rfl⟩
      obtain ⟨a₁, ha₁, hq₁⟩ := (Q.mem_iff I J h q).mp hq
      obtain ⟨a₂, ha₂, hz₂⟩ := (F.mem_iff I J h z).mp hz
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (q • z) = ((a₁ : Ω) • q) • ((a₂ : Ω) • z) := by
        rw [Subalgebra.coe_mul, smul_eq_mul, smul_smul, smul_smul]
        congr 1
        ring
      rw [e]
      exact Submodule.subset_span ⟨_, hq₁, _, hz₂, rfl⟩
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro y₁ y₂ _ _ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
          a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_add, smul_smul, smul_smul, Subalgebra.coe_mul,
          mul_comm (a₂ : Ω) (a₁ : Ω)]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
    · rintro b z _ ⟨a, ha, hz⟩
      obtain ⟨c, hc, hcb⟩ := exists_isUnit_mul_mem h b
      refine ⟨c * a, by rw [map_mul]; exact hc.mul ha, ?_⟩
      have e : ((c * a : chartRing S x I) : Ω) • (b • z) =
          (⟨_, hcb⟩ : chartRing S x I) • ((a : Ω) • z) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, Subalgebra.coe_mul]
        congr 1
        ring
      rw [e]
      exact Submodule.smul_mem _ _ hz
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (F.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ

def SubFamily.twistFam (F : SubFamily S x E) (Q : SubFamily S x Ω) : SubFamily S x E where
  toSubSystem := F.toSubSystem.twist Q.toSubSystem
  mem_iff := F.mem_twist_iff Q

theorem SubFamily.exists_pow (Q : SubFamily S x Ω) (n : ℕ) :
    ∃ P : SubFamily S x Ω, P.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨(twistBundle S x 0).toSubFamily, rfl⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P.twistFam Q, ?_⟩
    change P.toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [hP]

end

theorem SubFamilyTwistPow.proof : SubFamilyTwistPow.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q a
  obtain ⟨P, hP⟩ := SubFamily.exists_pow Q a
  exact ⟨F.twistFam P, by rw [← hP]; rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelTwistGenerated.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IsNoetherianRing S → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ β : K → ℤ,
      ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IndefiniteRowSideFullHecke.Kleiman2.IsGenerated S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SectionsPoly.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∃ P : MvPolynomial K ℚ, FieldNumbers.EventuallyPoly (NumbersDVR.hilbFn (mIdealOver F y)) P ∧
        ∀ β : K → ℤ, ∀ᶠ c : ℕ in Filter.atTop,
          (Module.finrank F (secOver F y (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) : ℚ) =
            eval (fun k => (((β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k : ℤ) : ℚ)) P

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutOneGeneratorSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def CutOneGenerator.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs →
    ¬ ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), L.sub (singleChart hj) ≤
      (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
        Submodule.span (chartRing k x (singleChart hj)) {s}

end

end GroundTheory.Heights₂.Heights.Kleiman
end
