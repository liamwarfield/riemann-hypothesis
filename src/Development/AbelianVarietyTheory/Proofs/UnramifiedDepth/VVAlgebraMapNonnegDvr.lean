module

public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem vV_algebraMap_nonneg_dvr (T : CDVR) (x : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr x) := by
  unfold vV valV
  rw [neg_nonneg]
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
    (IsDiscreteValuationRing.maximalIdeal T.V) x
  by_cases h0 : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
      (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr x) = 0
  · rw [h0, WithZero.log_zero]
  · rw [WithZero.log_le_iff_le_exp h0]
    simpa using h1

theorem nval_eq_of_extension :
    ∀ (T : CDVR) (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l ≠ 0 → v (l : C) = 1 → ∀ (ι : T.Fr →+* C), (∀ x : T.Fr, x ≠ 0 → v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((l : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)) → (∀ x : T.V, ((0 : ℝ) : WithTop ℝ) ≤ v (ι (algebraMap T.V T.Fr x))) ∧ ∀ x : T.Fr, nval T.V (vV T.V ((l : ℕ) : T.Fr)).toNat x = (WithBot.some (v (ι x)) : WithBot (WithTop ℝ)) := by
  intro T C _ v l hl hv ι hι
  have hvl : 0 ≤ vV T.V ((l : ℕ) : T.Fr) := by
    have h := vV_algebraMap_nonneg_dvr T (l : T.V)
    rwa [map_natCast] at h
  have hcast : (((vV T.V ((l : ℕ) : T.Fr)).toNat : ℕ) : ℝ) = ((vV T.V ((l : ℕ) : T.Fr) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hvl]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : algebraMap T.V T.Fr x ≠ 0 := fun h =>
        hx ((IsFractionRing.injective T.V T.Fr) (by rw [h, map_zero]))
      rw [hι _ hx']
      have h1 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr x) : ℝ) := by
        exact_mod_cast vV_algebraMap_nonneg_dvr T x
      have h2 : (0 : ℝ) ≤ (vV T.V ((l : ℕ) : T.Fr) : ℝ) := by exact_mod_cast hvl
      exact WithTop.coe_le_coe.mpr (div_nonneg h1 h2)
  · unfold nval
    split_ifs with hx
    · subst hx
      simp only [map_zero, AddValuation.map_zero]
      rfl
    · rw [hι x hx, hcast]
      rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroup
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma nv_eq_nEval {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n d : ℕ} (f : PS R n d)
    (a : Fin n → Fin d → S) :
    nv (algebraMap R S) f a = nEval f (fun q : Fin n × Fin d => a q.1 q.2) := by
  unfold nv nEval tEval
  rfl

private lemma sep_nil {R : Type} [CommRing R] {n d : ℕ} (f f' : PS R n d)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), (∀ i j, IsNilpotent (a i j)) →
      nv (algebraMap R S) f a = nv (algebraMap R S) f' a) : f = f' :=
  GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq R ⊥ inferInstance n d f f' (fun S _ _ _ _ _ a ha => h S a ha)

private lemma nv_ev {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n m d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (b : Fin m → Fin d → PS R n d) (f : PS R m d)
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) :
    nv s (ev b f) a = nv s f (fun i j => nv s (b i j) a) :=
  (nv_calculus R S s n d a ha).2.2.1 m d b f hb

private lemma nv_X {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) (j : Fin d) :
    nv s (MvPowerSeries.X (i, j)) a = a i j := by
  obtain ⟨ψ, h1, -, h3⟩ := (nv_calculus R S s n d a ha).1
  rw [← h1, h3]

private lemma nv_zero {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) :
    nv s (0 : PS R n d) a = 0 := by
  obtain ⟨ψ, h1, -, -⟩ := (nv_calculus R S s n d a ha).1
  rw [← h1, map_zero]

private lemma nilpotent_eval_subst_pair {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (b c : Fin d → PS R n d) (f : PS R 2 d)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0) :
    nv s (ev ![b, c] f) a = nv s f ![fun j => nv s (b j) a, fun j => nv s (c j) a] := by
  rw [nv_ev s a ha _ f (by intro i j; fin_cases i; exacts [hb j, hc j])]
  congr 1
  funext i j
  fin_cases i <;> rfl

private lemma const_pt {R : Type} [CommRing R] {n d : ℕ} (i : Fin n) (j : Fin d) :
    MvPowerSeries.constantCoeff (pt R d i j) = 0 := by
  simp [pt]

private lemma nv_pt {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) :
    (fun j => nv s (pt R d i j) a) = a i := funext fun j => nv_X s a ha i j

private lemma nv_at_zero {R : Type} [CommRing R] {n d : ℕ} (f : PS R n d) :
    nv (algebraMap R R) f (0 : Fin n → Fin d → R) = MvPowerSeries.constantCoeff f := by
  have := (nv_calculus R R (algebraMap R R) n d 0 (fun _ _ => IsNilpotent.zero)).2.2.2.2.2
    (fun _ _ _ _ => by simp) f
  simpa using this

private lemma constantCoeff_germEvalTwo_eq_zero {R : Type} [CommRing R] {n d : ℕ} (b c : Fin d → PS R n d) (f : PS R 2 d)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev ![b, c] f) = 0 := by
  rw [← nv_at_zero, nilpotent_eval_subst_pair _ _ (fun _ _ => IsNilpotent.zero) _ _ _ hb hc, ← hf, ← nv_at_zero]
  congr 1
  funext i j
  fin_cases i
  · exact (nv_at_zero _).trans (hb j)
  · exact (nv_at_zero _).trans (hc j)

theorem exists_nilChart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∃ (F : FGLaw R g) (X : Fam G g), NilChart G F.F X := by
  intro R _ _ G _ _ g hG
  classical
  obtain ⟨x, h0, hnat, hinj, hsur⟩ := GlobalTheory.NilCoord.nilpotent_coordinates G g hG
  have hser := @GlobalTheory.exists_series_of_natural_on_nilpotent (@GlobalTheory.nEval_basic)
  obtain ⟨F0, hF0⟩ := GlobalTheory.ChLaw.groupLaw_powerSeries (@GlobalTheory.nEval_basic) (@hser) G g x ⟨h0, hnat, hinj, hsur⟩
  have hF : ∀ k : Fin g, ∃ f : PS R 2 g, ∀ (S : Type) [CommRing S] [Algebra R S] (u : Fin 2 × Fin g → S),
      (∀ i, IsNilpotent (u i)) → fAdd F0 (fun j => u (0, j)) (fun j => u (1, j)) k = nEval f u := by
    intro k
    refine hser (fun S _ _ u => fAdd F0 (fun j => u (0, j)) (fun j => u (1, j)) k) ?_
    intro S _ _ S' _ _ φ u hu
    unfold fAdd
    rw [((GlobalTheory.nEval_basic (F0 k) S _).2 (by rintro (i | i) <;> exact hu _)).1 S' φ]
    congr 1
    funext i
    rcases i with i | i <;> rfl
  choose F hF using hF
  have hFe : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → fAdd F0 a b = fun k => nv (algebraMap R S) (F k) ![a, b] := by
    intro S _ _ a b ha hb
    funext k
    rw [nv_eq_nEval, ← hF k S _ (by rintro ⟨i, j⟩; fin_cases i; exacts [ha j, hb j])]
    rfl
  have law : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → x S a * x S b = x S (fun k => nv (algebraMap R S) (F k) ![a, b]) := by
    intro S _ _ a b ha hb
    rw [← hFe S a b ha hb]
    exact (hF0 S a b ha hb).2
  have nil : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (nv (algebraMap R S) (F k) ![a, b]) := by
    intro S _ _ a b ha hb k
    have h1 := (hF0 S a b ha hb).1 k
    rw [hFe S a b ha hb] at h1
    have h : Ideal.span (Set.range a ∪ Set.range b) ≤ nilradical S := Ideal.span_le.2 (by
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      exacts [mem_nilradical.2 (ha i), mem_nilradical.2 (hb i)])
    exact mem_nilradical.1 (h h1)
  have hz : ∀ (S : Type) [CommRing S] (i : Fin g), IsNilpotent ((0 : Fin g → S) i) :=
    fun S _ i => IsNilpotent.zero
  have unitL : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (fun k => nv (algebraMap R S) (F k) ![0, a]) = a := by
    intro S _ _ a ha
    refine hinj S _ _ (nil S _ _ (hz S) ha) ha ?_
    rw [← law S _ _ (hz S) ha, h0, _root_.one_mul]
  have const : ∀ k, MvPowerSeries.constantCoeff (F k) = 0 := by
    intro k
    have h := congrFun (unitL R 0 (hz R)) k
    rw [← nv_at_zero]
    refine Eq.trans ?_ h
    congr 1
    funext i j
    fin_cases i <;> rfl
  refine ⟨⟨F, const, ?_, ?_, ?_⟩, x, ⟨h0, hnat, hinj, ?_, law⟩⟩
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha (0 : Fin g → PS R 1 g) _ _ (fun _ => map_zero _) (const_pt _), nv_pt _ a ha, nv_X _ a ha]
    have e : (fun j => nv (algebraMap R S) ((0 : Fin g → PS R 1 g) j) a) = 0 :=
      funext fun j => nv_zero _ a ha
    rw [e]
    exact congrFun (unitL S (a 0) (ha 0)) k
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (const_pt _), nv_pt _ a ha, nv_pt _ a ha]
    have e : a = ![a 0, a 1] := by
      funext i
      fin_cases i <;> rfl
    conv_rhs => rw [e]
    refine congrFun (hinj S _ _ (nil S _ _ (ha 1) (ha 0)) (nil S _ _ (ha 0) (ha 1)) ?_) k
    rw [← law S _ _ (ha 1) (ha 0), ← law S _ _ (ha 0) (ha 1), _root_.mul_comm]
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha _ _ _ (fun l => constantCoeff_germEvalTwo_eq_zero _ _ _ (const_pt _) (const_pt _) (const l)) (const_pt _),
      nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (fun l => constantCoeff_germEvalTwo_eq_zero _ _ _ (const_pt _) (const_pt _) (const l))]
    simp only [nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (const_pt _), nv_pt _ a ha]
    refine congrFun (hinj S _ _ (nil S _ _ (nil S _ _ (ha 0) (ha 1)) (ha 2))
      (nil S _ _ (ha 0) (nil S _ _ (ha 1) (ha 2))) ?_) k
    rw [← law S _ _ (nil S _ _ (ha 0) (ha 1)) (ha 2), ← law S _ _ (ha 0) (nil S _ _ (ha 1) (ha 2)),
      ← law S _ _ (ha 0) (ha 1), ← law S _ _ (ha 1) (ha 2), _root_.mul_assoc]
  · intro S _ _ S' _ _ ρ σ hρσ hn z hz'
    refine hsur S S' ρ (fun y => ⟨σ y, AlgHom.congr_fun hρσ y⟩) ?_ z hz'
    intro c hc
    obtain ⟨N, hN⟩ := hn
    have := Ideal.pow_mem_pow hc N
    rw [hN] at this
    exact ⟨N, by simpa using this⟩

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroupStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nilpotentGroupChart_smooth_commGroup : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∃ (F : FGLaw R g) (X : Fam G g), NilChart G F.F X := by
  first | exact @GlobalTheory.ChF.exists_nilChart | exact GlobalTheory.ChF.exists_nilChart | (intros; apply GlobalTheory.ChF.exists_nilChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNMap
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MapDofNIterate
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.InvDerCopiesMap

open MvPowerSeries

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv (R := R) i f) = pderiv (R := S) i (MvPowerSeries.map φ f) := by
  ext m
  simp [coeff_map, coeff_pderiv]

theorem map_ev_axis {d n : ℕ} (b : Fin n) (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := n) ![pt R d b, 0] g) =
      ev (n := n) ![pt S d b, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  have h : HasSubst (fun p : Fin 2 × Fin d => (![pt R d b, 0] : Fin 2 → Pt R n d) p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    rintro ⟨j, i⟩
    fin_cases j <;> simp [pt]
  rw [MvPowerSeries.map_subst h]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> simp [pt]

theorem map_DofN {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f : PS R n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [DofN, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]

theorem map_DofN_iterate {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f : PS R n d) :
    MvPowerSeries.map φ ((DofN F b u)^[k] f) =
      (DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)))^[k] (MvPowerSeries.map φ f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_DofN, ih]

theorem map_DmonN {d n : ℕ} (F : Fin d → PS R 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R n d) :
    MvPowerSeries.map φ (DmonN F cp u m f) =
      DmonN (fun i => MvPowerSeries.map φ (F i)) cp (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, map_DofN_iterate, ih]

end GlobalTheory.InvDerCopiesMap

namespace GlobalTheory

theorem dpolyN_map : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (d n : ℕ) (F : Fin d → PS S 2 d) (κ : Type) [Fintype κ] (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) (f : PS S n d), DpolyN (fun i => MvPowerSeries.map ψ (F i)) cp (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) (MvPowerSeries.map ψ f) = MvPowerSeries.map ψ (DpolyN F cp u P f) := by
  intro S S' _ _ ψ d n F κ _ cp u P f
  unfold DpolyN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_subset (MvPolynomial.support_map_subset ψ P) (fun m _ hm => by
    rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.map_C, InvDerCopiesMap.map_DmonN, MvPolynomial.coeff_map]

end GlobalTheory
end
end

set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory


open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange in
theorem nabValN_map : ∀ (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] (ψ : S →+* S') (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (B' : FB S' d O), (∀ i, B'.G.F i = MvPowerSeries.map ψ (B.G.F i)) → (∀ a i, B'.A.act a i = MvPowerSeries.map ψ (B.A.act a i)) → ∀ (h : PS S 2 d), MvPowerSeries.constantCoeff h = 0 → ∀ (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ] (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S), nabValN B' S' (MvPowerSeries.map ψ h) w0 m (MvPowerSeries.map ψ f) cp (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) = ψ (nabValN B S h w0 m f cp u P) := by
  intro S S' _ _ _ _ ψ d O _ _ B B' hF hA h hc w0 m n f κ _ cp u P
  have eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B'.FK S' := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) =
      MvPowerSeries.map (algebraMap S' S') (B'.G.F i)
    rw [hF]
    ext e
    simp [coeff_map]
  have eA : mapP ψ (B.actK S w0) = B'.actK S' w0 := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) =
      MvPowerSeries.map (algebraMap S' S') (B'.A.act w0 i)
    rw [hA]
    ext e
    simp [coeff_map]
  have gC : GP (comp1 (B.actK S w0) (pt S (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL S h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map ψ (B.hL S h w0) = B'.hL S' (MvPowerSeries.map ψ h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]
  have g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j) := by
    intro b j
    fin_cases j
    exact gp_pt b
  have cb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt S d b] (B.hL S h w0)) = 0 :=
    fun b => gt_const_ev _ (g1 b) _ cL
  have eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n := n) ![pt S d b] (B.hL S h w0)) =
      ev (n := n) ![pt S' d b] (B'.hL S' (MvPowerSeries.map ψ h) w0) := by
    intro b
    rw [map_ev ψ _ (g1 b), eL]
    congr 1
    funext j
    fin_cases j
    exact baseChange_pt ψ b
  unfold nabValN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul,
    map_expS _ _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,
    Finset.sum_congr rfl fun b _ => eb b]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCombinationOfMemHaO
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemHHaOfCoeffFunctional
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoeffFunctional

open MvPolynomial

variable {σ K L : Type} [Field K] [Field L] [Algebra K L]

def coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ μ ∈ P.support, monomial μ (φ (P.coeff μ))

theorem coeff_coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) (μ : σ →₀ ℕ) :
    (coeffMap φ P).coeff μ = φ (P.coeff μ) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

theorem coeffMap_add (φ : L →ₗ[K] K) (P Q : MvPolynomial σ L) :
    coeffMap φ (P + Q) = coeffMap φ P + coeffMap φ Q := by
  ext μ
  simp [coeff_coeffMap]

theorem coeffMap_zero (φ : L →ₗ[K] K) : coeffMap φ (0 : MvPolynomial σ L) = 0 := by
  ext μ
  simp [coeff_coeffMap]

theorem coeffMap_map_mul_C (φ : L →ₗ[K] K) (A : MvPolynomial σ K) (c : L) :
    coeffMap φ (MvPolynomial.C c * MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.C (φ c) * A := by
  ext μ
  rw [coeff_coeffMap, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm c, ← Algebra.smul_def,
    map_smul, smul_eq_mul, mul_comm]

theorem coeffMap_comm (φ : L →ₗ[K] K) (f : MvPolynomial σ L →ₗ[L] MvPolynomial σ L)
    (g : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (h : ∀ A, f (MvPolynomial.map (algebraMap K L) A) = MvPolynomial.map (algebraMap K L) (g A))
    (P : MvPolynomial σ L) : coeffMap φ (f P) = g (coeffMap φ P) := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), coeffMap_add, coeffMap_add, map_add (f := _), hp, hq]
  | monomial μ c =>
    have e : (monomial μ c : MvPolynomial σ L) =
        MvPolynomial.C c * MvPolynomial.map (algebraMap K L) (monomial μ 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, coeffMap_map_mul_C, C_mul', map_smul, h, ← C_mul', coeffMap_map_mul_C, C_mul', C_mul',
      map_smul]

variable {T : Type} (r : T → ℕ) (n : ℕ)

theorem lap_one_map (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ'))
    (A : MvPolynomial (Letter T r n) K) :
    lap r n L 1 τ τ' a a' (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (lap r n K 1 τ τ' a a' A) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  by_cases hb : b = b'
  · subst hb
    simp [pderiv_map]
  · simp [Matrix.one_apply_ne hb]

theorem rowShift_map (s : T) (i i' : Fin (r s)) (t : K) (A : MvPolynomial (Letter T r n) K) :
    rowShift r n L s i i' (algebraMap K L t) (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (rowShift r n K s i i' t A) := by
  induction A using MvPolynomial.induction_on with
  | C c => simp [rowShift]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p l hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp

theorem mem_HHa_of_coeff_functional :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (K C : Type) [Field K] [Field C] [Algebra K C] (φ : C →ₗ[K] K) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C) (Q : MvPolynomial (Letter T r n) K), (∀ μ, Q.coeff μ = φ (P.coeff μ)) → P ∈ HHa r n C cc isX a → Q ∈ HHa r n K cc isX a := by
  intro T r n K L _ _ _ φ cc isX a P Q hQ hP
  have hQ' : Q = coeffMap φ P := by
    ext μ
    rw [hQ, coeff_coeffMap]
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [hQ', ← coeffMap_comm φ _ _ (lap_one_map r n τ (cc τ) b b') P, h1 τ hτ b b', coeffMap_zero]
  · intro s i i' hi t
    have := coeffMap_comm φ (rowShift r n L s i i' (algebraMap K L t)).toLinearMap
      (rowShift r n K s i i' t).toLinearMap (rowShift_map r n s i i' t) P
    simp only [AlgHom.toLinearMap_apply] at this
    rw [hQ', ← this, h2 s i i' hi]
  · intro m hm
    refine h3 m ?_
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [hQ, h0, map_zero])

end GlobalTheory.CoeffFunctional
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralBasisLinearCoordinates
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem exists_integral_basis_linear_coordinates :
    ∀ (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] [Algebra K C] (R : Subring C), (∀ x : V, algebraMap K C (algebraMap V K x) ∈ R) → ∀ s : Finset C, (∀ x ∈ s, x ∈ R) → ∃ (r : ℕ) (c : Fin r → C) (φ : Fin r → (C →ₗ[K] K)), (∀ j, c j ∈ R) ∧ ∀ x ∈ s, (∀ j, φ j x ∈ (algebraMap V K).range) ∧ x = ∑ j, algebraMap K C (φ j x) * c j := by
  intro V K C _ _ _ _ _ _ _ _ R hR s hs
  classical
  letI : Algebra V C := ((algebraMap K C).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap V C) :=
    (algebraMap K C).injective.comp (IsFractionRing.injective V K)
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hinj
  let M : Submodule V C := Submodule.span V (s : Set C)
  haveI : Module.Finite V M := Module.Finite.span_of_finite V s.finite_toSet
  haveI : Module.Free V M := inferInstance
  have hMR : ∀ x ∈ M, x ∈ R := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact R.zero_mem
    | add x y _ _ hx hy => exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def]
      exact R.mul_mem (hR a) hx
  let b := Module.finBasis V M
  let c : Fin (Module.finrank V M) → C := fun j => (b j : C)
  have hcV : LinearIndependent V c :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hcK : LinearIndependent K c := (LinearIndependent.iff_fractionRing V K).1 hcV
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K c).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (by
      exact hcK.fintypeLinearCombination_injective))
  refine ⟨_, c, fun j => (LinearMap.proj j).comp g, fun j => hMR _ (b j).2, ?_⟩
  intro x hx
  have hxM : x ∈ M := Submodule.subset_span hx
  have h1 : x = Fintype.linearCombination K c (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j)) := by
    have := congrArg Subtype.val (b.sum_repr ⟨x, hxM⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at this
    rw [Fintype.linearCombination_apply]
    simp only [algebraMap_smul]
    exact this.symm
  have h2 : g x = fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j) := by
    have := LinearMap.congr_fun hg (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j))
    rw [LinearMap.comp_apply, ← h1] at this
    exact this
  refine ⟨fun j => ⟨b.repr ⟨x, hxM⟩ j, ?_⟩, ?_⟩
  · simp [h2]
  · simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2, ← Algebra.smul_def]
    rw [Fintype.linearCombination_apply] at h1
    exact h1

end GlobalTheory
end

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem exists_integral_combination_of_mem_HaO :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] (e : K →+* C) (R : Subring C), (∀ x : V, e (algebraMap V K x) ∈ R) → ∀ (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C), P ∈ HaO r n C R cc isX a → ∃ (s : ℕ) (c : Fin s → C) (Q : Fin s → MvPolynomial (Letter T r n) K), (∀ j, c j ∈ R) ∧ (∀ j, Q j ∈ HaO r n K (algebraMap V K).range cc isX a) ∧ P = ∑ j, MvPolynomial.C (c j) * MvPolynomial.map e (Q j) := by
  intro T r n V K C _ _ _ _ _ _ _ e R hR cc isX a P hP
  classical
  let _ : Algebra K C := e.toAlgebra
  obtain ⟨hH, hO⟩ := hP
  obtain ⟨s, c, φ, hc, hφ⟩ := GlobalTheory.exists_integral_basis_linear_coordinates V K C R hR (P.support.image fun μ => P.coeff μ) (by
    intro x hx
    obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
    exact hO μ)
  let Q : Fin s → MvPolynomial (Letter T r n) K := fun j =>
    ∑ μ ∈ P.support, MvPolynomial.monomial μ (φ j (P.coeff μ))
  have hQ : ∀ j μ, (Q j).coeff μ = φ j (P.coeff μ) := by
    intro j μ
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
  refine ⟨s, c, Q, hc, fun j => ⟨GlobalTheory.CoeffFunctional.mem_HHa_of_coeff_functional T r n K C (φ j) cc isX a P (Q j) (hQ j) hH, ?_⟩, ?_⟩
  · intro μ
    rw [hQ]
    by_cases h : μ ∈ P.support
    · exact (hφ _ (Finset.mem_image_of_mem _ h)).1 j
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
      exact zero_mem _
  · ext μ
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hQ]
    by_cases h : μ ∈ P.support
    · refine (hφ _ (Finset.mem_image_of_mem _ h)).2.trans ?_
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · rw [MvPolynomial.notMem_support_iff.mp h]
      simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NablaValueCopiesBilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NablaValueCopiesBilinear
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

section NabLin

variable {R : Type} [CommRing R] {d n : ℕ}

theorem dofN_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f g : PS R n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem dofN_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (t : R) (f : PS R n d) :
    DofN F b u (t • f) = t • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, map_smul, mul_smul_comm, Finset.smul_sum]

theorem dofN_iterate_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f g : PS R n d) :
    (DofN F b u)^[k] (f + g) = (DofN F b u)^[k] f + (DofN F b u)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_add]

theorem dofN_iterate_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (t : R) (f : PS R n d) :
    (DofN F b u)^[k] (t • f) = t • (DofN F b u)^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_smul]

variable {ι : Type} [Fintype ι]

theorem dmonN_add (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (f g : PS R n d) :
    DmonN F cp u m (f + g) = DmonN F cp u m f + DmonN F cp u m g := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_add]

theorem dmonN_smul (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (t : R) (f : PS R n d) :
    DmonN F cp u m (t • f) = t • DmonN F cp u m f := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_smul]

theorem dpolyN_eq_sum_of_subset (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f : PS R n d) (s : Finset (ι →₀ ℕ)) (hs : P.support ⊆ s) :
    DpolyN F cp u P f = ∑ m ∈ s, MvPowerSeries.C (P.coeff m) * DmonN F cp u m f := by
  unfold DpolyN
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm, map_zero, zero_mul]

theorem dpolyN_add_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f g : PS R n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, dmonN_add, mul_add, Finset.sum_add_distrib]

theorem dpolyN_smul_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (t : R) (f : PS R n d) :
    DpolyN F cp u P (t • f) = t • DpolyN F cp u P f := by
  simp only [DpolyN, dmonN_smul, mul_smul_comm, Finset.smul_sum]

theorem dpolyN_add_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P Q : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (P + Q) f = DpolyN F cp u P f + DpolyN F cp u Q f := by
  classical
  rw [dpolyN_eq_sum_of_subset F cp u (P + Q) f (P.support ∪ Q.support) MvPolynomial.support_add,
    dpolyN_eq_sum_of_subset F cp u P f (P.support ∪ Q.support) Finset.subset_union_left,
    dpolyN_eq_sum_of_subset F cp u Q f (P.support ∪ Q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem dpolyN_C_mul_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (t : R) (P : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (MvPolynomial.C t * P) f = MvPowerSeries.C t * DpolyN F cp u P f := by
  have hs : (MvPolynomial.C t * P).support ⊆ P.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_C_mul, h0, mul_zero])
  rw [dpolyN_eq_sum_of_subset F cp u _ f P.support hs, DpolyN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, mul_assoc]

end NabLin

theorem nabValN_bilinear : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u
  refine ⟨fun f g P => ?_, fun t f P => ?_, fun f P Q => ?_, fun t f P => ?_⟩
  · simp only [nabValN, add_mul, dpolyN_add_right, map_add (f := _)]
  · simp only [nabValN]
    rw [smul_mul_assoc, dpolyN_smul_right, MvPowerSeries.smul_eq_C_mul, map_mul,
      MvPowerSeries.constantCoeff_C]
  · simp only [nabValN, dpolyN_add_left, map_add (f := _)]
  · simp only [nabValN]
    rw [dpolyN_C_mul_left, map_mul, MvPowerSeries.constantCoeff_C]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NablaValueCopiesBilinearStatement
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaValueCopies_bilinear : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by
  first | exact @GlobalTheory.nabValN_bilinear | exact GlobalTheory.nabValN_bilinear | (intros; apply GlobalTheory.nabValN_bilinear <;> assumption)
end
end
