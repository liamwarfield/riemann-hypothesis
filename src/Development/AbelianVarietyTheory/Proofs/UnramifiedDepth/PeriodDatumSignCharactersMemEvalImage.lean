module

public import ReciprocityTheory.DualLattices.StdJForm4
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FiniteAlgebraSplitLocal
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HtDualExists
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffDecomp
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChartPSmulLiftEqBt
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvHopfOfTensorLocal
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniversalDerivation
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvCotOfUnivDer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FAddNsmulFEqEvalPolyFrob
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private def btPolySub (p : ℕ) (g : ℕ) (W : Type) [CommRing W] :
    Subalgebra W (MvPolynomial (Fin g) W) where
  carrier := {q | ∀ m : Fin g →₀ ℕ, (∃ i, ¬ p ∣ m i) →
    AddMonoidAlgebra.coeff q m ∈ Ideal.span {(p : W)}}
  add_mem' := by
    intro a b ha hb m hm
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact Ideal.add_mem _ (ha m hm) (hb m hm)
  mul_mem' := by
    intro a b ha hb m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h1 : p ∣ x.1 i
    · refine Ideal.mul_mem_left _ _ (hb _ ⟨i, fun h2 => hi ?_⟩)
      rw [← hx', Finsupp.add_apply]
      exact dvd_add h1 h2
    · exact Ideal.mul_mem_right _ _ (ha _ ⟨i, h1⟩)
  algebraMap_mem' := by
    intro r m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C, ite_eq_right]
    · exact Ideal.zero_mem _
    · rintro rfl
      exact hi (by simp)

private lemma btPoly_map_tEval {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (f : MvPowerSeries ι R₀) {S S' : Type} [CommRing S] [Algebra R₀ S] [CommRing S']
    [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : ι → S) :
    φ (tEval N f a) = tEval N f (fun i => φ (a i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [tEval, map_sum, map_prod]

private lemma btPoly_unif {ι S : Type} [Fintype ι] [CommRing S] (a : ι → S)
    (h : ∀ i, IsNilpotent (a i)) : ∃ M, ∀ M' ≥ M, ∀ i, a i ^ M' = 0 := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun M' hM i => ?_⟩
  exact pow_eq_zero_of_le ((Finset.le_sup (Finset.mem_univ i)).trans hM) (hn i)

private lemma btPoly_nil {R₀ : Type} [CommRing R₀]
    (H : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S]
      [Algebra R₀ S] (a : ι → S), (∀ i, IsNilpotent (a i)) →
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))
    {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S]
    (a : Fin g → S) (ha : ∀ i, IsNilpotent (a i)) (n : ℕ) :
    ∀ k, IsNilpotent (nsmulF ch.F a n k) := by
  have h0 : ∀ k, algebraMap R₀ S (MvPowerSeries.coeff 0 (ch.F k)) = 0 := by
    intro k
    have h1 := congrFun (ch.F_unit S 0 (fun _ => IsNilpotent.zero)) k
    have h2 := H (ch.F k) S (Sum.elim (0 : Fin g → S) (0 : Fin g → S))
      (by rintro (i | i) <;> exact IsNilpotent.zero)
    have h3 : Ideal.span (Set.range (Sum.elim (0 : Fin g → S) (0 : Fin g → S))) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i | i, rfl⟩ <;> rfl
    rw [h3, Ideal.mem_bot] at h2
    change nEval _ _ = 0 at h1
    rw [h1] at h2
    simpa using h2
  induction n with
  | zero => intro k; exact IsNilpotent.zero
  | succ n ih =>
    intro k
    have hn : ∀ i, IsNilpotent (Sum.elim (nsmulF ch.F a n) a i) := by
      rintro (i | i)
      · exact ih i
      · exact ha i
    have h2 := H (ch.F k) S _ hn
    rw [h0, sub_zero] at h2
    have h3 : Ideal.span (Set.range (Sum.elim (nsmulF ch.F a n) a)) ≤ nilradical S := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hn i
    exact h3 h2

theorem fAdd_nsmulF_eq_eval_poly_frob :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} (K : LAlg R₀) (ch : FormalChartAtZero B K g), PSerFrobStatement p K ch) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (W : Type) [CommRing W] [Algebra R₀ W] (c : Fin g → W),
    (∀ i, IsNilpotent (c i)) → ∀ N : ℕ, ∃ Γ : Fin g → MvPolynomial (Fin g) W,
      (∀ k m, (∃ i, ¬ p ∣ m i) → AddMonoidAlgebra.coeff (Γ k) m ∈ Ideal.span {(p : W)}) ∧
      ∀ y : Fin g → W, (∀ i, y i ^ N = 0) → fAdd ch.F c (nsmulF ch.F y p) = fun k => MvPolynomial.eval y (Γ k)) := by
  intro H1 H2 R₀ _ p _ g B K ch W _ _ c hc N
  obtain ⟨G, hG, hGe⟩ := H2 p K ch N
  let I : Ideal (MvPolynomial (Fin g) R₀) := Ideal.span (Set.range fun j => MvPolynomial.X j ^ N)
  let x : Fin g → MvPolynomial (Fin g) R₀ ⧸ I := fun j => Ideal.Quotient.mk I (MvPolynomial.X j)
  have hx : ∀ j, x j ^ N = 0 := fun j => by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hae : (MvPolynomial.aeval x : MvPolynomial (Fin g) R₀ →ₐ[R₀] _) = Ideal.Quotient.mkₐ R₀ I := by
    ext j; simp [x]
  have hnil : ∀ k, IsNilpotent (Ideal.Quotient.mk I (G k)) := fun k => by
    have := btPoly_nil (fun f S _ _ a ha => ((H1 f S a).2 ha).2) ch _ x (fun i => ⟨N, hx i⟩) p k
    rw [hGe _ x hx, hae] at this
    exact this
  obtain ⟨M₁, hM₁⟩ := btPoly_unif _ hnil
  obtain ⟨M₂, hM₂⟩ := btPoly_unif _ hc
  let z : Fin g ⊕ Fin g → MvPolynomial (Fin g) W :=
    Sum.elim (fun i => MvPolynomial.C (c i)) (fun i => MvPolynomial.map (algebraMap R₀ W) (G i))
  refine ⟨fun k => tEval (max M₁ M₂) (ch.F k) z, fun k => ?_, fun y hy => ?_⟩
  · change tEval (max M₁ M₂) (ch.F k) z ∈ btPolySub p g W
    unfold tEval
    refine Subalgebra.sum_mem _ fun e _ => Subalgebra.mul_mem _ ?_
      (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · rw [IsScalarTower.algebraMap_apply R₀ W]
      exact Subalgebra.algebraMap_mem _ _
    · rcases i with i | i
      · exact Subalgebra.algebraMap_mem (btPolySub p g W) (c i)
      · intro m hm
        obtain ⟨r, hr⟩ := hG i m hm
        change AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap R₀ W) (G i)) m ∈ _
        rw [MvPolynomial.coeff_map, hr, map_mul, map_natCast]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · funext k
    have hI : ∀ q ∈ I, MvPolynomial.aeval y q = (0 : W) := by
      intro q hq
      have : I ≤ RingHom.ker (MvPolynomial.aeval y : MvPolynomial (Fin g) R₀ →ₐ[R₀] W) := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        simp [RingHom.mem_ker, hy j]
      exact this hq
    have e1 := btPoly_map_tEval (max M₁ M₂) (ch.F k)
      ((MvPolynomial.aeval y : MvPolynomial (Fin g) W →ₐ[W] W).restrictScalars R₀) z
    have e2 : (fun i => ((MvPolynomial.aeval y : MvPolynomial (Fin g) W →ₐ[W] W).restrictScalars R₀)
        (z i)) = Sum.elim c (fun k => MvPolynomial.aeval y (G k)) := by
      funext i
      rcases i with i | i
      · simp [z]
      · simp only [z, AlgHom.coe_restrictScalars', Sum.elim_inr]
        exact MvPolynomial.aeval_map_algebraMap W y (G i)
    rw [e2] at e1
    rw [hGe W y hy]
    change nEval _ _ = _
    rw [(H1 (ch.F k) W _).1 (max M₁ M₂), ← e1]
    · simp
    · rintro (i | i)
      · exact hM₂ _ (le_max_right _ _) i
      · have := hM₁ _ (le_max_left M₁ M₂) i
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at this
        have := hI _ this
        rwa [map_pow] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvImgIsLatSubring
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

section

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)

end

theorem _root_.GlobalTheory.evImg_isLat_subring :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvLatStatement D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D
  unfold _root_.ReciprocityTheory.PGsh.Be2.EvLatStatement
  intro C _ _ hdom hinj
  classical
  letI inst : ∀ i, Algebra Tw.O.carrier (D.fin.AAx i).carrier := fun i =>
    ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
  have hspec : ∀ t, (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.LHom.id _ ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t := fun t => by
    have h := (D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) (_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t) (D.pt_p t)).choose_spec.choose_spec
    exact ⟨h.1, h.2.1⟩
  let ev : ∀ t : _root_.ReciprocityTheory.PGsh.Up.Nb p g, (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] Tw.O.carrier := fun t =>
    { toRingHom := ((D.ptMap t).1 : (D.fin.AAx (D.ptIdx t)).carrier →+* Tw.O.carrier).comp
        (Pi.evalRingHom _ (D.ptIdx t))
      commutes' := fun o => by
        have h := congrArg (fun φ : _root_.ReciprocityTheory.PGsh.LHom Tw.O Tw.O => φ.1 o) (hspec t).1
        exact h }
  let Ψ : (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → Tw.O.carrier) :=
    Pi.algHom _ _ ev
  let f : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → C) :=
    (Algebra.linearMap Tw.O.carrier C).compLeft (_root_.ReciprocityTheory.PGsh.Up.Nb p g) ∘ₗ Ψ.toLinearMap
  have hf : ∀ F x, f F x = algebraMap _ C ((D.ptMap x).1 (F (D.ptIdx x))) := fun F x => rfl
  have himg : D.evImg C = LinearMap.range f := by
    unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg _root_.ReciprocityTheory.PGsh.Be2.Dat.evAll
    change Submodule.span _ (Set.range ⇑f) = _
    rw [← LinearMap.coe_range, Submodule.span_eq]
  have hinjΨ : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    funext i
    apply D.fin.sep i
    intro φ hφ
    have hz : p • B.map φ (D.fin.y i) = 0 := by rw [← map_nsmul, D.fin.y_p, map_zero]
    obtain ⟨t, ht⟩ := D.L.τ_basis.2 ⟨_, hz⟩
    have ht' : _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t = B.map φ (D.fin.y i) := congrArg Subtype.val ht
    obtain ⟨i0, φ0, -, -, huniq⟩ := D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ hz
    obtain ⟨hi, hφ0⟩ := huniq i φ hφ rfl
    obtain ⟨hi', hψ0⟩ := huniq (D.ptIdx t) (D.ptMap t) (hspec t).1 ((hspec t).2.trans ht')
    subst hi
    have key : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), j = i → HEq ψ φ →
        ψ.1 (F j) = φ.1 (F i) := by
      rintro j ψ rfl h
      rw [eq_of_heq h]
    exact (key _ _ hi' (hψ0.trans hφ0.symm)).symm.trans (congrFun hF t)
  haveI : ∀ i, Module.Free Tw.O.carrier (D.fin.AAx i).carrier := fun i => (D.fin.free i).1
  haveI : ∀ i, Module.Finite Tw.O.carrier (D.fin.AAx i).carrier := fun i => (D.fin.free i).2
  haveI := hdom
  have hrank : Module.finrank Tw.O.carrier (∀ i, (D.fin.AAx i).carrier) = Fintype.card (_root_.ReciprocityTheory.PGsh.Up.Nb p g) := by
    rw [Module.finrank_pi_fintype, ← Nat.card_eq_fintype_card]
    refine Eq.trans ?_ (D.fin.rank.trans (Nat.card_congr (Equiv.ofBijective _ D.L.τ_basis)).symm)
    rfl
  let b0 := Module.Free.chooseBasis Tw.O.carrier (∀ i, (D.fin.AAx i).carrier)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex Tw.O.carrier (∀ i, (D.fin.AAx i).carrier)) =
      Fintype.card (_root_.ReciprocityTheory.PGsh.Up.Nb p g) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hrank]
  let b := b0.reindex (Fintype.equivOfCardEq hcard)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.PGsh.L2.IsLat
    refine ⟨Matrix.of fun x j => f (b j) x, ?_, ?_⟩
    · rw [isUnit_iff_ne_zero]
      have hdet : (Matrix.of fun x j => f (b j) x).det =
          algebraMap Tw.O.carrier C (Matrix.of fun x j => Ψ (b j) x).det := by
        rw [RingHom.map_det]; rfl
      rw [hdet]
      intro h0
      rw [← map_zero (algebraMap Tw.O.carrier C)] at h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (hinj h0)
      apply hv0
      have hsum : Ψ (∑ j, v j • b j) = 0 := by
        rw [← hv]
        funext x
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, map_sum, map_smul, mul_comm]
      have h1 : ∑ j, v j • b j = 0 := hinjΨ (by rw [hsum, map_zero])
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent v h1 j
    · rw [himg]
      change _ = Submodule.span _ (Set.range (f ∘ b))
      rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
  · rw [himg]
    rintro _ ⟨F, rfl⟩
    exact fun x => ⟨_, (hf F x).symm⟩
  · rw [himg]
    exact ⟨1, by funext x; simp only [hf, Pi.one_apply, map_one]⟩
  · rw [himg]
    rintro _ _ ⟨F, rfl⟩ ⟨G, rfl⟩
    exact ⟨F * G, by funext x; simp only [hf, Pi.mul_apply, map_mul]⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LocalFactorModPNilOver
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private theorem exists_localFactor_lemma {R₀ : Type} [CommRing R₀] {O R K A : _root_.ReciprocityTheory.PGsh.LAlg R₀}
    (q : _root_.ReciprocityTheory.PGsh.LHom O R) (hq : Function.Surjective q.1) (c : O.carrier)
    (hker : RingHom.ker (q.1 : O.carrier →+* R.carrier) = Ideal.span {c})
    (ρ : _root_.ReciprocityTheory.PGsh.LHom R K) (hρ : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρ) (hK : maximalIdeal K.carrier = ⊥)
    (s : _root_.ReciprocityTheory.PGsh.LHom O A) (hfin : (s.1 : O.carrier →+* A.carrier).Finite)
    (φ₀ : _root_.ReciprocityTheory.PGsh.LHom A O) (hφ₀ : φ₀.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O) :
    ∃ (Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀) (μ : _root_.ReciprocityTheory.PGsh.LHom A Λ) (j : _root_.ReciprocityTheory.PGsh.LHom R Λ) (ρΛ : _root_.ReciprocityTheory.PGsh.LHom Λ K),
      _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = ρ ∧ μ.comp s = j.comp q ∧
      ∀ φ : _root_.ReciprocityTheory.PGsh.LHom A O, φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O →
        ∃ ψ : _root_.ReciprocityTheory.PGsh.LHom Λ R, ψ.comp μ = q.comp φ ∧ ψ.comp j = _root_.ReciprocityTheory.PGsh.LHom.id R ∧ ρ.comp ψ = ρΛ := by
  classical
  have hmR : ∀ x ∈ maximalIdeal R.carrier, IsNilpotent x := by
    intro x hx
    apply hρ.2
    haveI := ρ.2
    have h1 : (ρ.1 : R.carrier →+* K.carrier) x ∈ maximalIdeal K.carrier := map_nonunit _ x hx
    rw [hK] at h1
    exact h1
  have hc0 : q.1 c = 0 := by
    have h1 : c ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier) := hker ▸ Ideal.mem_span_singleton_self c
    exact h1
  have hc : ¬ IsUnit c := by
    intro hu
    have h1 := hu.map q.1
    rw [hc0] at h1
    exact not_isUnit_zero h1
  have hsc : ¬ IsUnit (s.1 c) := by
    haveI := s.2
    exact fun h => hc ((isUnit_map_iff (s.1 : O.carrier →+* A.carrier) c).1 h)
  set I : Ideal A.carrier := Ideal.span {s.1 c} with hI
  have hItop : I ≠ ⊤ := by
    rw [hI, Ne, Ideal.span_singleton_eq_top]
    exact hsc
  haveI : Nontrivial (A.carrier ⧸ I) := _root_.ReciprocityTheory.PGsh.Ainf.quot_nontrivial I hItop
  haveI : IsLocalRing (A.carrier ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀ := _root_.ReciprocityTheory.PGsh.LAlg.mk (A.carrier ⧸ I)
  let μ : _root_.ReciprocityTheory.PGsh.LHom A Λ := ⟨Ideal.Quotient.mkₐ R₀ I,
    _root_.ReciprocityTheory.PGsh.TowerExample.isLocalHom_of_surj ((Ideal.Quotient.mkₐ R₀ I : A.carrier →ₐ[R₀] A.carrier ⧸ I) : A.carrier →+* A.carrier ⧸ I)
      (Ideal.Quotient.mkₐ_surjective R₀ I)⟩
  have hqc : ∀ a ∈ RingHom.ker q.1, ((Ideal.Quotient.mkₐ R₀ I).comp s.1) a = 0 := by
    intro a ha
    have ha' : a ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier) := ha
    rw [hker, Ideal.mem_span_singleton'] at ha'
    obtain ⟨b, rfl⟩ := ha'
    rw [AlgHom.comp_apply, map_mul, map_mul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), mul_zero]
  let j₀ : R.carrier →ₐ[R₀] A.carrier ⧸ I :=
    (Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc).comp
      (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom
  have hj₀ : ∀ x, j₀ (q.1 x) = Ideal.Quotient.mk I (s.1 x) := by
    intro x
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x) =
        Ideal.Quotient.mk (RingHom.ker q.1) x := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc
      ((Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x)) = _
    rw [h1]
    rfl
  have hj₀loc : IsLocalHom (j₀ : R.carrier →+* A.carrier ⧸ I) := by
    constructor
    intro x hx
    by_contra hxu
    obtain ⟨n, hn⟩ := hmR x ((mem_maximalIdeal x).2 hxu)
    have h1 : IsUnit ((j₀ : R.carrier →+* A.carrier ⧸ I) x ^ n) := hx.pow n
    rw [← map_pow, hn, map_zero] at h1
    exact not_isUnit_zero h1
  let j : _root_.ReciprocityTheory.PGsh.LHom R Λ := ⟨j₀, hj₀loc⟩
  have hψI : ∀ φ : _root_.ReciprocityTheory.PGsh.LHom A O, φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → ∀ a ∈ I, (q.1.comp φ.1) a = 0 := by
    intro φ hφ a ha
    rw [hI, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    have h1 : φ.1 (s.1 c) = c := congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O O => f.1 c) hφ
    rw [AlgHom.comp_apply, map_mul, map_mul, h1, hc0, mul_zero]
  let ψ₀ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → (A.carrier ⧸ I →ₐ[R₀] R.carrier) :=
    fun φ hφ => Ideal.Quotient.liftₐ I (q.1.comp φ.1) (hψI φ hφ)
  have hψ₀mk : ∀ φ hφ a, ψ₀ φ hφ (Ideal.Quotient.mk I a) = q.1 (φ.1 a) := fun _ _ _ => rfl
  have hψ₀loc : ∀ φ hφ, IsLocalHom (ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier) := by
    intro φ hφ
    constructor
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : IsUnit (q.1 (φ.1 a)) := hx
    haveI := q.2
    haveI := φ.2
    have h2 : IsUnit (φ.1 a) := isUnit_of_map_unit (q.1 : O.carrier →+* R.carrier) _ h1
    have h3 : IsUnit a := isUnit_of_map_unit (φ.1 : A.carrier →+* O.carrier) _ h2
    exact h3.map (Ideal.Quotient.mk I)
  let ψ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → _root_.ReciprocityTheory.PGsh.LHom Λ R :=
    fun φ hφ => ⟨ψ₀ φ hφ, hψ₀loc φ hφ⟩
  have hψj : ∀ φ hφ r, ψ₀ φ hφ (j₀ r) = r := by
    intro φ hφ r
    obtain ⟨x, rfl⟩ := hq r
    rw [hj₀, hψ₀mk φ hφ]
    exact congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O R => f.1 x)
      (show q.comp (φ.comp s) = q.comp (_root_.ReciprocityTheory.PGsh.LHom.id O) by rw [hφ])
  have hkerm : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = 0 →
      l ∈ maximalIdeal (A.carrier ⧸ I) := by
    intro φ hφ l hl
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (ρ.1 (ψ₀ φ hφ l)) := (hu.map (ψ₀ φ hφ)).map ρ.1
    rw [hl] at h1
    exact not_isUnit_zero h1
  have hmK : ∀ φ hφ (l : A.carrier ⧸ I), l ∈ maximalIdeal (A.carrier ⧸ I) →
      ρ.1 (ψ₀ φ hφ l) = 0 := by
    intro φ hφ l hl
    haveI := hψ₀loc φ hφ
    haveI := ρ.2
    have h1 : (ρ.1 : R.carrier →+* K.carrier) ((ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier) l) ∈
        maximalIdeal K.carrier :=
      map_nonunit _ _ (map_nonunit _ l hl)
    rw [hK] at h1
    exact h1
  have hagree : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = ρ.1 (ψ₀ φ₀ hφ₀ l) := by
    intro φ hφ l
    have h1 : ρ.1 (ψ₀ φ₀ hφ₀ (l - j₀ (ψ₀ φ₀ hφ₀ l))) = 0 := by
      rw [map_sub, hψj φ₀ hφ₀ (ψ₀ φ₀ hφ₀ l), sub_self, map_zero]
    have h2 := hmK φ hφ _ (hkerm φ₀ hφ₀ _ h1)
    rw [map_sub, map_sub, hψj φ hφ (ψ₀ φ₀ hφ₀ l), sub_eq_zero] at h2
    exact h2
  have hcomp : (Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier) =
      (j₀ : R.carrier →+* A.carrier ⧸ I).comp (q.1 : O.carrier →+* R.carrier) := by
    ext x
    exact (hj₀ x).symm
  have hint : ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier)).IsIntegral :=
    ((RingHom.Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).comp
      hfin).to_isIntegral
  refine ⟨Λ, μ, j, ρ.comp (ψ φ₀ hφ₀), ⟨fun k => ?_, fun l hl => ?_⟩,
    Ideal.Quotient.mkₐ_surjective R₀ I, ?_, ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := hρ.1 k
    refine ⟨j₀ r, ?_⟩
    show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r
    rw [hψj φ₀ hφ₀ r]
  · have hl' : ρ.1 (ψ₀ φ₀ hφ₀ l) = 0 := hl
    have hm := hkerm φ₀ hφ₀ l hl'
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hJR : J.comap (j₀ : R.carrier →+* A.carrier ⧸ I) = maximalIdeal R.carrier := by
      have hP : (J.comap (j₀ : R.carrier →+* A.carrier ⧸ I)).IsPrime := Ideal.comap_isPrime _ J
      apply le_antisymm
      · exact le_maximalIdeal hP.ne_top
      · intro x hx
        obtain ⟨n, hn⟩ := hmR x hx
        exact hP.mem_of_pow_mem n (by rw [hn]; exact Ideal.zero_mem _)
    have hmax : (J.comap ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier))).IsMaximal := by
      rw [hcomp, ← Ideal.comap_comap, hJR]
      exact Ideal.comap_isMaximal_of_surjective (q.1 : O.carrier →+* R.carrier) hq
    have hJmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ hint J hmax
    rw [eq_maximalIdeal hJmax]
    exact hm
  · exact Subtype.ext (AlgHom.ext fun r => by
      show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r
      rw [hψj φ₀ hφ₀ r])
  · exact Subtype.ext (AlgHom.ext fun x => by
      show Ideal.Quotient.mk I (s.1 x) = j₀ (q.1 x)
      exact (hj₀ x).symm)
  · intro φ hφ
    refine ⟨ψ φ hφ, Subtype.ext (AlgHom.ext fun a => rfl),
      Subtype.ext (AlgHom.ext fun r => hψj φ hφ r), Subtype.ext (AlgHom.ext fun l => hagree φ hφ l)⟩

theorem _root_.GlobalTheory.localFactor_mod_p_nilOver :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀) (μ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Λ) (j : _root_.ReciprocityTheory.PGsh.LHom (Tw.R 0) Λ) (ρΛ : _root_.ReciprocityTheory.PGsh.LHom Λ D.K),
      _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O →
        ∃ ψ : _root_.ReciprocityTheory.PGsh.LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = _root_.ReciprocityTheory.PGsh.LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D hg
  have hid : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver (_root_.ReciprocityTheory.PGsh.LHom.id D.K) :=
    ⟨fun x => ⟨x, rfl⟩, fun a ha => ⟨1, by rw [pow_one]; exact (RingHom.mem_ker).1 ha⟩⟩
  have hK : maximalIdeal (D.K : Type) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hsub : ∀ u v : {x // (B.map (_root_.ReciprocityTheory.PGsh.LHom.id D.K)) x = 0}, u = v := by
      intro u v
      have hu := u.2
      have hv := v.2
      rw [B.map_id] at hu hv
      exact Subtype.ext (hu.trans hv.symm)
    have h1 : (fun _ : Fin g => (⟨a, ha⟩ : maximalIdeal (D.K : Type))) = fun _ => 0 :=
      (D.ch.χ (_root_.ReciprocityTheory.PGsh.LHom.id D.K) hid).symm.injective (hsub _ _)
    have h2 := congrFun h1 ⟨0, hg⟩
    exact (Ideal.mem_bot).2 (congrArg Subtype.val h2)
  have hW := D.sm.nil
  have heq := D.wd.ρW_eq
  have hρ1 : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1 := by
    refine ⟨fun k => ?_, fun a ha => ?_⟩
    · obtain ⟨w, hw⟩ := hW.1 k
      refine ⟨D.wd.πW.1 w, ?_⟩
      rw [← hw, ← heq]
      rfl
    · obtain ⟨w, rfl⟩ := D.wd.πW_surj a
      have hw : w ∈ RingHom.ker (D.wd.ρW.1 : D.wd.W.carrier →+* D.K.carrier) := by
        rw [RingHom.mem_ker, ← heq]
        exact (RingHom.mem_ker).1 ha
      exact (hW.2 w hw).map (D.wd.πW.1 : D.wd.W.carrier →+* (Tw.R 0).carrier)
  refine ⟨hK, hρ1, fun i => ?_⟩
  have hsec : ∃ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : (D.fin.AAx i).carrier) = 0 := D.fin.sep i 1 fun φ hφ => absurd hφ (hne φ)
    exact one_ne_zero h1
  obtain ⟨φ₀, hφ₀⟩ := hsec
  have hfin : ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).Finite := by
    letI : Algebra Tw.O.carrier (D.fin.AAx i).carrier :=
      ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
    exact (D.fin.free i).2
  exact exists_localFactor_lemma (Tw.q 0) D.tower_zero_surjective (p : Tw.O.carrier) D.tower_zero_ker D.wd.ρ1 hρ1 hK
    (D.fin.sO i) hfin φ₀ hφ₀

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChartFirstOrderMemSpan
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private lemma chartFirstOrder_mem_span {S : Type} [CommRing S] {g : ℕ} (a : Fin g → S)
    (x : TrivSqZeroExt S (Fin g → S))
    (hx : x ∈ Ideal.span (Set.range fun i => (TrivSqZeroExt.inl (a i) : TrivSqZeroExt S (Fin g → S)))) :
    x.fst ∈ Ideal.span (Set.range a) ∧ ∀ j, x.snd j ∈ Ideal.span (Set.range a) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨Ideal.subset_span ⟨i, rfl⟩, fun j => by simp⟩
  | zero => exact ⟨by simp, fun j => by simp⟩
  | add y z _ _ hy hz =>
    exact ⟨by simpa using add_mem hy.1 hz.1, fun j => by simpa using add_mem (hy.2 j) (hz.2 j)⟩
  | smul r y _ hy =>
    refine ⟨?_, fun j => ?_⟩
    · rw [smul_eq_mul, TrivSqZeroExt.fst_mul]
      exact Ideal.mul_mem_left _ _ hy.1
    · rw [smul_eq_mul, TrivSqZeroExt.snd_mul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      exact add_mem (Ideal.mul_mem_left _ _ (hy.2 j)) (Ideal.mul_mem_left _ _ hy.1)

theorem chart_fAdd_firstOrder :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) := by
  intro H R₀ _ g B K ch S _ _ a ha

  have nat : ∀ (T : Type) [CommRing T] [Algebra R₀ T] (T' : Type) [CommRing T'] [Algebra R₀ T']
      (φ : T →ₐ[R₀] T') (x y : Fin g → T), (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) →
      ∀ k, φ (fAdd ch.F x y k) = fAdd ch.F (fun i => φ (x i)) (fun i => φ (y i)) k := by
    intro T _ _ T' _ _ φ x y hx hy k
    have h := ((H (ch.F k) T (Sum.elim x y)).2 (by rintro (i | i); exacts [hx i, hy i])).1 T' φ
    unfold fAdd
    rw [h]
    congr 1
    funext i
    cases i <;> rfl

  let T := TrivSqZeroExt S (Fin g → S)
  let a' : Fin g → T := fun i => TrivSqZeroExt.inl (a i)
  let e' : Fin g → T := fun j => TrivSqZeroExt.inr (Pi.single j 1)
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => (ha i).map (TrivSqZeroExt.inlHom S (Fin g → S))
  have he' : ∀ i, IsNilpotent (e' i) := fun i => ⟨2, by
    rw [pow_two]; exact TrivSqZeroExt.inr_mul_inr _ _ _⟩
  have hfst : ∀ k, (fAdd ch.F a' e' k).fst = a k := by
    intro k
    have h := nat T S (TrivSqZeroExt.fstHom R₀ S (Fin g → S)) a' e' ha' he' k
    have h2 := congrFun (ch.F_unit S a ha) k
    rw [← h2]
    exact h
  refine ⟨fun k j => (fAdd ch.F a' e' k).snd j, ?_, ?_⟩
  · intro k j
    let J : Ideal T := Ideal.span (Set.range a')
    have h := nat T (T ⧸ J) (Ideal.Quotient.mkₐ R₀ J) a' e' ha' he' k
    have h0 : (fun i => Ideal.Quotient.mkₐ R₀ J (a' i)) = 0 := by
      funext i
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    have hn : ∀ i, IsNilpotent (Ideal.Quotient.mkₐ R₀ J (e' i)) := fun i => (he' i).map _
    rw [h0, ch.F_comm _ 0 _ (fun _ => IsNilpotent.zero) hn, ch.F_unit _ _ hn] at h
    have hm : fAdd ch.F a' e' k - e' k ∈ J := Ideal.Quotient.eq.1 h
    have := (chartFirstOrder_mem_span a _ hm).2 j
    rw [TrivSqZeroExt.snd_sub] at this
    have h1 : (1 : Matrix (Fin g) (Fin g) S) k j = (e' k).snd j := by
      simp only [e', TrivSqZeroExt.snd_inr, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [h1]
    exact this
  · intro e he
    let l : (Fin g → S) →ₗ[R₀] S :=
      { toFun := fun v => v ⬝ᵥ e
        map_add' := fun v w => add_dotProduct _ _ _
        map_smul' := fun r v => smul_dotProduct _ _ _ }
    have hl : ∀ v, l v = v ⬝ᵥ e := fun _ => rfl
    let φ : T →ₐ[R₀] S := TrivSqZeroExt.lift (AlgHom.id R₀ S) l
      (fun v w => by
        simp only [hl, dotProduct, Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [mul_mul_mul_comm, he, mul_zero])
      (fun r v => by simp [hl])
      (fun r v => by simp [hl, mul_comm])
    have hφ : ∀ x : T, φ x = x.fst + x.snd ⬝ᵥ e := fun _ => rfl
    funext k
    have h := nat T S φ a' e' ha' he' k
    have e1 : (fun i => φ (a' i)) = a := by
      funext i; simp [hφ, a']
    have e2 : (fun i => φ (e' i)) = e := by
      funext i; simp [hφ, e']
    rw [e1, e2, hφ, hfst] at h
    rw [← h]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffDvdOfAevalAddSqZero
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private lemma polCoef_taylor {R₀ A : Type} [CommRing R₀] [CommRing A] [Algebra R₀ A] {g : ℕ}
    (a : Fin g → A) (i : Fin g) (ε : A) (hε : ε * ε = 0) (G : MvPolynomial (Fin g) R₀) :
    MvPolynomial.aeval (a + Pi.single i ε) G
      = MvPolynomial.aeval a G + MvPolynomial.aeval a (MvPolynomial.pderiv i G) * ε := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add f h hf hh => simp only [map_add (f := _), hf, hh]; ring
  | mul_X f j hf =>
    simp only [map_mul, hf, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul, map_add (f := _),
      MvPolynomial.pderiv_X, Pi.add_apply]
    by_cases hij : j = i
    · subst hij
      simp only [Pi.single_eq_same, map_one]
      linear_combination (MvPolynomial.aeval a (MvPolynomial.pderiv j f)) * hε
    · simp only [Pi.single_eq_of_ne hij, map_zero]
      ring

private lemma polCoef_pderiv {R₀ : Type} [CommRing R₀] (p : ℕ) {g N : ℕ}
    (G : MvPolynomial (Fin g) R₀)
    (H : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S,
      (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G)
    {A : Type} [CommRing A] [Algebra R₀ A] (hpA : (p : A) = 0) (x : Fin g → A)
    (hx : ∀ j, x j ^ N = 0) (i : Fin g) :
    MvPolynomial.aeval x (MvPolynomial.pderiv i G) = 0 := by
  have hpS : (p : DualNumber A) = 0 := by
    rw [← map_natCast (algebraMap A (DualNumber A)), hpA, map_zero]
  let φ : A →ₐ[R₀] DualNumber A := IsScalarTower.toAlgHom R₀ A (DualNumber A)
  let a : Fin g → DualNumber A := fun j => φ (x j)
  have h1 := H (DualNumber A) hpS a (Pi.single i DualNumber.eps)
    (fun j => by simp only [a]; rw [← map_pow, hx, map_zero])
    (fun j k => by
      by_cases hj : j = i
      · by_cases hk : k = i
        · subst hj; subst hk
          rw [Pi.single_eq_same, DualNumber.eps_mul_eps]
        · rw [Pi.single_eq_of_ne hk, mul_zero]
      · rw [Pi.single_eq_of_ne hj, zero_mul])
  rw [polCoef_taylor a i _ DualNumber.eps_mul_eps] at h1
  have h2 : MvPolynomial.aeval a (MvPolynomial.pderiv i G) * DualNumber.eps = 0 :=
    add_eq_left.mp h1
  have h3 : MvPolynomial.aeval a (MvPolynomial.pderiv i G)
      = φ (MvPolynomial.aeval x (MvPolynomial.pderiv i G)) := by
    rw [MvPolynomial.comp_aeval_apply]
  rw [h3] at h2
  generalize MvPolynomial.aeval x (MvPolynomial.pderiv i G) = y at h2 ⊢
  have := congrArg TrivSqZeroExt.snd h2
  simpa [φ, TrivSqZeroExt.algebraMap_eq_inl] using this

private lemma polCoef_span {R : Type} [CommRing R] {g N : ℕ} (f : MvPolynomial (Fin g) R)
    (hf : f ∈ Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R) ^ N)) :
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → AddMonoidAlgebra.coeff f m = 0 := by
  rw [Ideal.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, rfl⟩ := hf
  intro m hm
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', if_neg]
  intro h
  have := h j
  simp only [Finsupp.single_eq_same] at this
  exact absurd (hm j) (not_lt.mpr this)

theorem coeff_dvd_of_aeval_add_sq_zero :
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g N : ℕ) (G : MvPolynomial (Fin g) R₀),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S, (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G) →
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → (∃ i, ¬ p ∣ m i) → ∃ r : R₀, AddMonoidAlgebra.coeff G m = p * r) := by
  intro R₀ _ p hp g N G H m hm ⟨i, hi⟩
  let I : Ideal R₀ := Ideal.span {(p : R₀)}
  let R := R₀ ⧸ I
  let J : Ideal (MvPolynomial (Fin g) R) :=
    Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R) ^ N)
  let A := MvPolynomial (Fin g) R ⧸ J
  have hpR : (p : R) = 0 := by
    have : (Ideal.Quotient.mk I) (p : R₀) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    simpa using this
  have hpA : (p : A) = 0 := by
    rw [← map_natCast (algebraMap R A), hpR, map_zero]
  let x : Fin g → A := fun j => Ideal.Quotient.mk J (MvPolynomial.X j)
  have hx : ∀ j, x j ^ N = 0 := fun j => by
    simp only [x]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩
  have h4 := polCoef_pderiv p G H hpA x hx i
  have h5 : ∀ f : MvPolynomial (Fin g) R₀, MvPolynomial.aeval x f
      = Ideal.Quotient.mk J (MvPolynomial.map (algebraMap R₀ R) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => simp only [MvPolynomial.aeval_C, MvPolynomial.map_C]; rfl
    | add f h hf hh => simp only [map_add (f := _), hf, hh]
    | mul_X f j hf => simp only [map_mul, hf, MvPolynomial.aeval_X, MvPolynomial.map_X, x]
  rw [h5, Ideal.Quotient.eq_zero_iff_mem] at h4
  have hpos : 1 ≤ m i := by
    rcases Nat.eq_zero_or_pos (m i) with h | h
    · exact absurd (h ▸ dvd_zero p) hi
    · exact h
  have h6 := polCoef_span _ h4 (m - Finsupp.single i 1)
    (fun j => lt_of_le_of_lt (by simp) (hm j))
  have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.mpr hpos
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_pderiv, tsub_add_cancel_of_le hle] at h6
  have h7 : AddMonoidAlgebra.coeff G m * (m i : R₀) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e : (((m - Finsupp.single i 1 : Fin g →₀ ℕ) i : ℕ) : R₀) + 1 = (m i : R₀) := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.cast_sub hpos]; simp
    rw [e] at h6
    exact h6
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h7
  have hc : IsCoprime (p : R₀) (m i : R₀) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hi)
  obtain ⟨u, v, huv⟩ := hc
  exact ⟨u * AddMonoidAlgebra.coeff G m + v * s, by
    linear_combination (-AddMonoidAlgebra.coeff G m) * huv - v * hs⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsLocalRingTensorProductOfFiniteOfPoints
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private theorem tenLocal_sub_mem {O A : Type} [CommRing O] [CommRing A] [IsLocalRing O]
    [IsLocalRing A] [Algebra O A] (φ : A →ₐ[O] O) (a : A) :
    a - algebraMap O A (φ a) ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have h2 := h.map φ
  simp at h2

theorem isLocalRing_tensorProduct_of_finite_of_points :
  (∀ (O A A' : Type) [CommRing O] [CommRing A] [CommRing A'] [IsLocalRing O] [IsLocalRing A] [IsLocalRing A'] [Algebra O A] [Algebra O A']
    [Module.Finite O A] [Module.Finite O A'], (A →ₐ[O] O) → (A' →ₐ[O] O) → IsLocalRing (A ⊗[O] A')) := by
  intro O A A' _ _ _ _ _ _ _ _ _ _ φ φ'
  let Φ : A ⊗[O] A' →ₐ[O] O := Algebra.TensorProduct.productMap φ φ'
  have hsurj : Function.Surjective Φ := fun o => ⟨algebraMap _ _ o, Φ.commutes o⟩
  have hM0 : ((maximalIdeal O).comap Φ).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective Φ hsurj
  refine IsLocalRing.of_unique_max_ideal ⟨(maximalIdeal O).comap Φ, hM0, ?_⟩
  intro M hM
  have hint : Algebra.IsIntegral O (A ⊗[O] A') := Algebra.IsIntegral.of_finite _ _
  have key : ∀ {B : Type} [CommRing B] [IsLocalRing B] [Algebra O B] (f : B →ₐ[O] A ⊗[O] A'),
      M.comap f = maximalIdeal B := by
    intro B _ _ _ f
    have hf : (f : B →+* A ⊗[O] A').IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap O B) _ ?_
      rw [f.comp_algebraMap]
      exact fun x => hint.isIntegral x
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (f : B →+* A ⊗[O] A') hf M
    exact IsLocalRing.eq_maximalIdeal this
  have hA := key (Algebra.TensorProduct.includeLeft : A →ₐ[O] A ⊗[O] A')
  have hA' := key (Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A')
  have hO := key (Algebra.ofId O (A ⊗[O] A'))
  have hx : ∀ x : A ⊗[O] A', x - algebraMap O _ (Φ x) ∈ M := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      have := M.add_mem hx hy
      rw [map_add (f := _), map_add (f := _)]
      convert this using 1
      ring
    | tmul a a' =>
      have h1 := tenLocal_sub_mem φ a
      have h2 := tenLocal_sub_mem φ' a'
      rw [← hA, Ideal.mem_comap, map_sub, AlgHom.commutes] at h1
      rw [← hA', Ideal.mem_comap, map_sub, AlgHom.commutes] at h2
      have h3 := M.add_mem
        (M.mul_mem_right ((Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A') a') h1)
        (M.mul_mem_left (algebraMap O (A ⊗[O] A') (φ a)) h2)
      have e1 : a ⊗ₜ[O] a' = (Algebra.TensorProduct.includeLeft : A →ₐ[O] A ⊗[O] A') a *
          (Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A') a' := by simp
      have e2 : Φ (a ⊗ₜ[O] a') = φ a * φ' a' := by simp [Φ]
      rw [e2, map_mul, e1]
      convert h3 using 1
      ring
  refine hM.eq_of_le hM0.ne_top ?_
  intro x hxM
  rw [Ideal.mem_comap, ← hO, Ideal.mem_comap]
  have := M.sub_mem hxM (hx x)
  simpa using this

end GlobalTheory
end

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

noncomputable section

namespace GlobalTheory.EvClose

theorem pSerFrob {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀}
    (K : LAlg R₀) (ch : FormalChartAtZero B K g) : PSerFrobStatement p K ch :=
  GlobalTheory.pSerFrob_of_invariance @GlobalTheory.nEval_basic
    (GlobalTheory.nsmulF_add_sqZero_eq @GlobalTheory.nEval_basic (GlobalTheory.chart_fAdd_firstOrder @GlobalTheory.nEval_basic))
    @GlobalTheory.coeff_dvd_of_aeval_add_sq_zero p K ch

theorem wFrob {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p}
    {K : LAlg R₀} (wd : WData Tw K) (g : ℕ) : WFrobStatement wd g :=
  GlobalTheory.WFrob.wFrob wd g

section Leaves

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)}

theorem evLat (D : Dat p g B Tw Dt Oe σ cp) : EvLatStatement D :=
  GlobalTheory.evImg_isLat_subring D

theorem evHopf (D : Dat p g B Tw Dt Oe σ cp) : EvHopfStatement D :=
  _root_.GlobalTheory.EvHopf.evHopf_of_tensorLocal
    GlobalTheory.isLocalRing_tensorProduct_of_finite_of_points D

theorem evAct (D : Dat p g B Tw Dt Oe σ cp) : EvActStatement D :=
  GlobalTheory.EvAct.evImg_act_stable D

theorem evHt (D : Dat p g B Tw Dt Oe σ cp) : EvHtStatement D :=
  GlobalTheory.evHt_of_lam @GlobalTheory.localFactor_mod_p_nilOver D

theorem evBt (D : Dat p g B Tw Dt Oe σ cp) : EvBtStatement D :=
  GlobalTheory.evBt_of_tangent_of_series
    (GlobalTheory.chart_p_smul_lift_eq_bt (GlobalTheory.chart_fAdd_firstOrder @GlobalTheory.nEval_basic))
    (GlobalTheory.fAdd_nsmulF_eq_eval_poly_frob @GlobalTheory.nEval_basic @pSerFrob)
    @GlobalTheory.localFactor_mod_p_nilOver @wFrob D

theorem periodDatum_signCharacters_mem_evalImage (D : Dat p g B Tw Dt Oe σ cp) : EvenTwoEvaluationSign D :=
  GlobalTheory.signChar_mem_evImg D

theorem evCot (D : Dat p g B Tw Dt Oe σ cp) : EvCotStatement D :=
  GlobalTheory.evCot_of_univDer (GlobalTheory.CotUniv.universal_derivation @GlobalTheory.CotPoints.points_eq_tangent) D

def htdOfDat (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] (v : Valuation C NNReal)
    [Algebra (Tw.O : Type) C] (hdom : IsDomain (Tw.O : Type))
    (hinj : Function.Injective (algebraMap (Tw.O : Type) C)) :
    HodgeTateDatum p g v (Tw.O : Type) Oe σ cp :=
  htd_of D C v hdom hinj (evLat D) (evHopf D) (evAct D) (evHt D) (evBt D) (periodDatum_signCharacters_mem_evalImage D) (evCot D)

end Leaves

end GlobalTheory.EvClose
