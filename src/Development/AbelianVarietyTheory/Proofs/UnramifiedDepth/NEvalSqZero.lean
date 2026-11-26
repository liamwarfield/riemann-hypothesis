module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteTorsOfFiniteTorsion
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.FormalGroupCoeffSecondLinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem nv_eq_sum {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ} (f : PS R n d)
    (a : Fin n → Fin d → S) (N : ℕ) (hN : ∀ q : Fin n × Fin d, a q.1 q.2 ^ N = 0) :
    nv s f a = ∑ e : Fin n × Fin d → Fin N, s (MvPowerSeries.coeff
      (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) f) * ∏ i, a i.1 i.2 ^ (e i : ℕ) := by
  letI := s.toAlgebra
  exact evBasic_nEval_eq_tEval f (fun q : Fin n × Fin d => a q.1 q.2) N hN

private theorem nEval_sqZero {R S κ : Type} [CommRing R] [CommRing S] [Algebra R S] [Fintype κ] [DecidableEq κ]
    (f : MvPowerSeries κ R) (a : κ → S) (ha : ∀ i, IsNilpotent (a i)) (h : ∀ i j, a i * a j = 0) :
    nEval f a = algebraMap R S (MvPowerSeries.constantCoeff f) +
      ∑ q, algebraMap R S (MvPowerSeries.coeff (Finsupp.single q 1) f) * a q := by
  have h0 : ∀ i : κ, IsNilpotent ((0 : κ → S) i) := fun _ => IsNilpotent.zero
  have hm : ∀ i, a i ∈ Ideal.span (Set.range a) := fun i => Ideal.subset_span ⟨i, rfl⟩
  have h1 := ChartCompare.nEval_sub_mem f a 0 ha h0 _ _ hm (fun _ => Ideal.zero_mem _)
    (fun i => by simpa using hm i)
  have h2 : Ideal.span (Set.range a) * Ideal.span (Set.range a) ≤ ⊥ := by
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact h i j
  have h3 := (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp) : Ideal.span _ ≤ (⊥ : Ideal S))
    (evBasic_nEval_sub_coeff_mem f (0 : κ → S) h0)
  have h4 := h2 h1
  rw [Ideal.mem_bot, sub_eq_zero] at h3 h4
  rw [h3, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, sub_eq_iff_eq_add'] at h4
  simpa [Algebra.smul_def] using h4

theorem nv_calculus : ∀ (R S : Type) [CommRing R] [CommRing S] (s : R →+* S) (n d : ℕ) (a : Fin n → Fin d → S), (∀ i j, IsNilpotent (a i j)) → (∃ ψ : PS R n d →+* S, (∀ f, ψ f = nv s f a) ∧ (∀ c, ψ (MvPowerSeries.C c) = s c) ∧ ∀ q : Fin n × Fin d, ψ (MvPowerSeries.X q) = a q.1 q.2) ∧ (∀ f : PS R n d, MvPowerSeries.constantCoeff f = 0 → IsNilpotent (nv s f a) ∧ nv s f a ∈ Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2)) ∧ (∀ (m e : ℕ) (b : Fin m → Fin e → PS R n d) (f : PS R m e), (∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) → nv s (sub b f) a = nv s f (fun i j => nv s (b i j) a)) ∧ (∀ (R' : Type) [CommRing R'] (β : R' →+* R) (f : PS R' n d), nv (s.comp β) f a = nv s (MvPowerSeries.map β f) a) ∧ (∀ (S' : Type) [CommRing S'] (t : S →+* S') (f : PS R n d), t (nv s f a) = nv (t.comp s) f (fun i j => t (a i j))) ∧ ((∀ i j i' j', a i j * a i' j' = 0) → ∀ f : PS R n d, nv s f a = s (MvPowerSeries.constantCoeff f) + ∑ q : Fin n × Fin d, s (MvPowerSeries.coeff (Finsupp.single q 1) f) * a q.1 q.2) := by
  intro R S _ _ s n d a ha
  have ha' : ∀ q : Fin n × Fin d, IsNilpotent (a q.1 q.2) := fun q => ha _ _
  obtain ⟨N, -, hN⟩ := evBasic_exists_pow (fun q : Fin n × Fin d => a q.1 q.2) ha'
  letI := s.toAlgebra
  refine ⟨?_, fun f hf => ⟨ChartCompare.isNilpotent_nEval f hf _ ha', ?_⟩, fun m e b f hb => ?_,
    fun R' _ β f => ?_, fun S' _ t f => ?_,
    fun h f => nEval_sqZero f (fun q : Fin n × Fin d => a q.1 q.2) ha' fun _ _ => h _ _ _ _⟩
  · let ψ : PS R n d →+* S := (MvPowerSeries.constantCoeff : MvPowerSeries Empty S →+* S).comp
      (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C _ ha')).toRingHom
    have hψ : ∀ f, ψ f = nv s f a := fun f => by
      simp [ψ, nv, MvPowerSeries.coe_substAlgHom, ChartCompare.subst_C_eq f _ ha']
    refine ⟨ψ, hψ, fun c => ?_, fun q => (hψ _).trans (ChartCompare.nEval_X _ ha' q)⟩
    have := (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C _ ha')).commutes c
    exact (congrArg MvPowerSeries.constantCoeff this).trans (by
      rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C]; rfl)
  · have := evBasic_nEval_sub_coeff_mem f _ ha'
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_zero, sub_zero] at this
    exact this
  · exact ChartCompare.nEval_subst (fun q : Fin m × Fin e => b q.1 q.2) (fun q => hb _ _) f _ ha'
  · rw [nv_eq_sum _ _ a N hN, nv_eq_sum _ _ a N hN]
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]
  · rw [nv_eq_sum _ _ a N hN, nv_eq_sum _ _ _ N (fun q => by rw [← map_pow, hN q, map_zero])]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_prod, map_pow, RingHom.comp_apply]

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentCharts
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private def dbl (R : Type) [CommRing R] {S : Type} [CommRing S] [Algebra R S] (J : Ideal S) :
    Subalgebra R (S × S) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R S S))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R S S))

private theorem mem_dbl {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S] {J : Ideal S}
    {x : S × S} : x ∈ dbl R J ↔ x.1 - x.2 ∈ J := by
  rw [← Ideal.Quotient.eq]; rfl

private theorem exists_coord {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {G' : Over (Spec (CommRingCat.of R))} [GrpObj G'] {d e : ℕ} {F : Fin d → PS R 2 d} {F' : Fin e → PS R 2 e}
    {X : Fam G d} {X' : Fam G' e} (h : NilChart G F X) (h' : NilChart G' F' X') (f : G ⟶ G') [IsMonHom f]
    (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ b : Fin e → S, (∀ j, IsNilpotent (b j)) ∧ X S a ≫ f = X' S b := by
  let J : Ideal S := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical ⟨(Set.finite_range a).toFinset, by simp [J]⟩, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ha i
  let ρ : dbl R J →ₐ[R] S := (AlgHom.fst R S S).comp (dbl R J).val
  let τ : dbl R J →ₐ[R] S := (AlgHom.snd R S S).comp (dbl R J).val
  let σ : S →ₐ[R] dbl R J := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict _ (fun x => by
    simp [mem_dbl])
  have hker : IsNilpotent (RingHom.ker ρ) := by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n + 1, le_bot_iff.1 fun x hx => ?_⟩
    have h1 : x ∈ RingHom.ker ρ := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
    have h2 : RingHom.ker ρ ≤ J.comap τ := fun y hy => by
      have h3 := mem_dbl.1 y.2
      have h4 : y.1.1 = 0 := hy
      rw [h4, zero_sub, neg_mem_iff] at h3
      exact h3
    have h5 := Ideal.le_comap_pow τ (n + 1) (Ideal.pow_right_mono h2 (n + 1) hx)
    rw [pow_succ, hn, zero_mul] at h5
    exact Subtype.ext (Prod.ext h1 h5)
  let a' : Fin d → dbl R J := fun i => ⟨(0, a i), mem_dbl.2 (by
    simpa using (Ideal.subset_span ⟨i, rfl⟩ : a i ∈ J))⟩
  have hnil : ∀ y : dbl R J, ρ y = 0 → IsNilpotent y := fun y hy => by
    obtain ⟨n, hn⟩ := hker
    exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow (show y ∈ RingHom.ker ρ from hy) n⟩
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => hnil _ rfl
  obtain ⟨b, hb, hz⟩ := h'.surj (dbl R J) S ρ σ (by ext; rfl) hker (X _ a' ≫ f) (by
    rw [← Category.assoc, h.nat _ _ ρ a' ha']
    have : (fun i => ρ (a' i)) = 0 := rfl
    rw [this, h.zero, MonObj.one_comp])
  refine ⟨fun j => τ (b j), fun j => (hnil _ (hb j)).map τ, ?_⟩
  rw [← h'.nat _ _ τ b (fun j => hnil _ (hb j)), ← hz, ← Category.assoc, h.nat _ _ τ a' ha']
  rfl

theorem exists_reads : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'] (d e : ℕ) (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (X : Fam G d) (X' : Fam G' e), NilChart G F X → NilChart G' F' X' → ∀ f : G ⟶ G', IsMonHom f → ∃ φ : Fin e → PS R 1 d, Reads X X' f φ := by
  intro R _ G _ _ G' _ _ d e F F' X X' h h' f hf
  classical
  choose b hb hX using exists_coord h h' f
  let c : Fin e → ∀ (S : Type) [CommRing S] [Algebra R S], (Fin 1 × Fin d → S) → S :=
    fun j S _ _ a => if ha : ∀ i, IsNilpotent (a (0, i)) then b S (fun i => a (0, i)) ha j else 0
  have hc : ∀ j (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S']
      (φ : S →ₐ[R] S') (a : Fin 1 × Fin d → S), (∀ i, IsNilpotent (a i)) →
      φ (c j S a) = c j S' (fun i => φ (a i)) := by
    intro j S _ _ S' _ _ φ a ha
    have h1 : ∀ i, IsNilpotent (a (0, i)) := fun i => ha _
    have h2 : ∀ i, IsNilpotent (φ (a (0, i))) := fun i => (ha _).map φ
    simp only [c, dif_pos h1, dif_pos h2]
    refine congrFun (h'.inj S' (fun j => φ (b S _ h1 j)) (b S' _ h2) (fun j => (hb S _ h1 j).map φ)
      (hb S' _ h2) ?_) j
    rw [← hX, ← h'.nat _ _ φ _ (hb S _ h1), ← hX, ← Category.assoc, h.nat _ _ φ _ h1]
  choose φ hφ using fun j => GlobalTheory.exists_series_of_natural_on_nilpotent GlobalTheory.nEval_basic (c j) (hc j)
  have key : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)),
      b S a ha = fun j => nv (algebraMap R S) (φ j) ![a] := by
    intro S _ inst a ha
    funext j
    have h1 := hφ j S (fun q => a q.2) (fun q => ha _)
    simp only [c, dif_pos ha] at h1
    rw [h1, nv]
    have : (algebraMap R S).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    rw [this]
    congr 1
    funext q
    obtain ⟨i, k⟩ := q
    fin_cases i
    rfl
  refine ⟨φ, fun j => ?_, fun S _ _ a ha => by rw [hX S a ha, key]⟩
  have h0 : ∀ i : Fin d, IsNilpotent ((0 : Fin d → R) i) := fun _ => IsNilpotent.zero
  have h1 : b R 0 h0 = 0 := h'.inj R _ _ (hb R 0 h0) (fun _ => IsNilpotent.zero) (by
    rw [← hX, h.zero, h'.zero, MonObj.one_comp])
  have h2 := hφ j R 0 (fun _ => IsNilpotent.zero)
  have h3 : c j R 0 = 0 := by
    exact (dif_pos h0).trans (congrFun h1 j)
  have h4 := (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp) : Ideal.span _ ≤ (⊥ : Ideal R))
    (evBasic_nEval_sub_coeff_mem (φ j) (0 : Fin 1 × Fin d → R) (fun _ => IsNilpotent.zero))
  rw [← h2, h3] at h4
  simpa using h4

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentChartsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_reading_groupHom_nilpotentCharts : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'] (d e : ℕ) (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (X : Fam G d) (X' : Fam G' e), NilChart G F X → NilChart G' F' X' → ∀ f : G ⟶ G', IsMonHom f → ∃ φ : Fin e → PS R 1 d, Reads X X' f φ := by
  first | exact @GlobalTheory.ChF.exists_reads | exact GlobalTheory.ChF.exists_reads | (intros; apply GlobalTheory.ChF.exists_reads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawJacobianExtensionChangeCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawJacobianExtensionChangeCoeff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma map_sub' {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (a' : Fin m → Fin d → PS S n e) (h : ∀ i j, MvPowerSeries.map β (a i j) = a' i j) :
    MvPowerSeries.map β (sub a f) = sub a' (MvPowerSeries.map β f) := by
  unfold sub
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2) (fun q => ha q.1 q.2))]
  simp only [h]

private lemma cc_sub {R : Type} [CommRing R] {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub a f) = 0 := by
  unfold sub
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
      (fun q => ha q.1 q.2)) (fun q => ha q.1 q.2) hf

private lemma ev_eq {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Fin d → PS R n d) (f : PS R m d) :
    ev a f = sub a f := rfl

private lemma map_pt {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.map β (pt R d j i) = pt S d j i := by simp [pt]

private lemma cc_pt {R : Type} [CommRing R] {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (pt R d j i) = 0 := by simp [pt]

private lemma map_subst_single {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d) :
    MvPowerSeries.map β (sub ![x] f) =
      sub ![fun j => MvPowerSeries.map β (x j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by fin_cases i; exact hx j) f _ (fun i j => by fin_cases i; rfl)

private lemma map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d) :
    MvPowerSeries.map β (sub ![x, y] f) =
      sub ![fun j => MvPowerSeries.map β (x j), fun j => MvPowerSeries.map β (y j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f _ (fun i j => by fin_cases i <;> rfl)

private lemma constCoeff_subst_single {R : Type} [CommRing R] {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x] f) = 0 :=
  cc_sub _ (fun i j => by fin_cases i; exact hx j) f hf

private lemma constantCoeff_sub2_eq_zero {R : Type} [CommRing R] {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x, y] f) = 0 :=
  cc_sub _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f hf

private lemma isHomF_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ}
    (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (φ : Fin e → PS R 1 d)
    (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0) (h : IsHomF F F' φ) :
    IsHomF (fun j => MvPowerSeries.map β (F j)) (fun j => MvPowerSeries.map β (F' j))
      (fun j => MvPowerSeries.map β (φ j)) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun j => by simp [MvPowerSeries.constantCoeff_map, h0], fun j => ?_⟩
  have := congrArg (MvPowerSeries.map β) (h1 j)
  simp only [ev_eq] at this ⊢
  rw [map_subst_single β _ hF, map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))
    (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))] at this
  simp only [map_subst_single β _ (cc_pt _), map_pt] at this
  exact this

private lemma lin_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ} (φ : Fin e → PS R 1 d) :
    lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β := by
  ext i j
  simp [lin, MvPowerSeries.coeff_map]

private noncomputable def mapLaw {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d : ℕ} (F : FGLaw R d) :
    FGLaw S d where
  F := F.mapF β
  const i := by simp [FGLaw.mapF, MvPowerSeries.constantCoeff_map, F.const]
  unit i := by
    have := congrArg (MvPowerSeries.map β) (F.unit i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun _ => by simp) (cc_pt _)] at this
    simp only [map_pt, Pi.zero_apply, map_zero, MvPowerSeries.map_X] at this
    exact this
  comm i := by
    have := congrArg (MvPowerSeries.map β) (F.comm i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _)] at this
    simp only [map_pt] at this
    exact this
  assoc i := by
    have := congrArg (MvPowerSeries.map β) (F.assoc i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l)) (cc_pt _),
      map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l))] at this
    simp only [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _), map_pt] at this
    exact this

theorem changeCoeff_law_lin_extSer : ∀ (R S : Type) [CommRing R] [CommRing S] (β : R →+* S), (∀ (d : ℕ) (F : FGLaw R d), ∃ F' : FGLaw S d, F'.F = F.mapF β) ∧ (∀ (d e : ℕ) (φ : Fin e → PS R 1 d), lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β) ∧ ∀ (d g r : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q → ExtSer (F.mapF β) (FB.mapF β) (fun j => MvPowerSeries.map β (J j)) (fun j => MvPowerSeries.map β (Q j)) := by
  intro R S _ _ β
  refine ⟨fun d F => ⟨mapLaw β F, rfl⟩, fun d e φ => lin_map β φ, fun d g r F FB J Q h => ⟨?_, ?_, ?_⟩⟩
  · have hg : (fun j => MvPowerSeries.map β (gmF R r j)) = gmF S r := by
      funext j; simp [gmF]
    rw [← hg]
    exact isHomF_map β _ _ _ (fun j => by simp [gmF]) h.homI
  · exact isHomF_map β _ _ _ F.const h.homQ
  · rw [lin_map, lin_map]
    obtain ⟨h0, A', B', h1, h2, h3⟩ := h.exact
    refine ⟨?_, A'.map β, B'.map β, ?_, ?_, ?_⟩
    · rw [← Matrix.map_mul, h0]; simp
    · rw [← Matrix.map_mul, h1]; simp
    · rw [← Matrix.map_mul, h2]; simp
    · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add β), h3]; simp

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawJacobianExtensionChangeCoeffStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLaw_jacobian_extension_changeCoeff : ∀ (R S : Type) [CommRing R] [CommRing S] (β : R →+* S), (∀ (d : ℕ) (F : FGLaw R d), ∃ F' : FGLaw S d, F'.F = F.mapF β) ∧ (∀ (d e : ℕ) (φ : Fin e → PS R 1 d), lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β) ∧ ∀ (d g r : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q → ExtSer (F.mapF β) (FB.mapF β) (fun j => MvPowerSeries.map β (J j)) (fun j => MvPowerSeries.map β (Q j)) := by
  first | exact @GlobalTheory.ChF.changeCoeff_law_lin_extSer | exact GlobalTheory.ChF.changeCoeff_law_lin_extSer | (intros; apply GlobalTheory.ChF.changeCoeff_law_lin_extSer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_comp_single {R : Type} [CommRing R] {d : ℕ} (φ ψ : Pt R 1 d)
    (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) : lin (comp1 φ ψ) = lin φ * lin ψ := by
  ext i j
  have h := coeff_lin_ev (m := 1) ![ψ] (by intro k l; fin_cases k; exact hψ l) (φ i) (0, j)
  rw [Fintype.sum_prod_type, Fin.sum_univ_one] at h
  rw [Matrix.mul_apply]
  exact h

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_formal_add {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (φ ψ : Pt R 1 d)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) : lin (F.add φ ψ) = lin φ + lin ψ := by
  ext i j
  have h := coeff_lin_ev (m := 2) ![φ, ψ]
    (by intro k l; fin_cases k; exacts [hφ l, hψ l]) (F.F i) (0, j)
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [formal_group_coeff_first_linear, formal_group_coeff_second_linear, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  exact h.trans (congrArg₂ (· + ·) (_root_.one_mul _) (_root_.one_mul _))

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_zero_point {R : Type} [CommRing R] {d : ℕ} : lin (pt R (n := 1) d 0) = 1 := by
  ext i j
  change MvPowerSeries.coeff _ (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 d) = _
  rw [coeff_X_single, Matrix.one_apply]
  simp [eq_comm]

theorem linPart_act_ringHom : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (OE : Type) [CommRing OE] (act : Geo.Tor.Germ.OAct OE F) (S : Type) [CommRing S] (β : R →+* S), ∃ ρ : OE →+* Matrix (Fin d) (Fin d) S, ∀ a, ρ a = linPart (actMap β act a) ∧ ρ a = (lin (act.act a)).map β := by
  intro R _ d F OE _ act S _ β
  let ρ₀ : OE →+* Matrix (Fin d) (Fin d) R := RingHom.mk'
    { toFun := fun a => lin (act.act a)
      map_one' := by rw [act.one_act, linear_part_zero_point]
      map_mul' := fun a b => by rw [act.mul_act, linear_part_comp_single _ _ (act.const b)] }
    (fun a b => by
      change lin (act.act (a + b)) = lin (act.act a) + lin (act.act b)
      rw [act.add_act, linear_part_formal_add _ _ _ (act.const a) (act.const b)])
  refine ⟨(β.mapMatrix).comp ρ₀, fun a => ⟨?_, rfl⟩⟩
  ext i j
  change β (MvPowerSeries.coeff _ (act.act a i)) =
    MvPowerSeries.coeff _ (MvPowerSeries.map β (act.act a i))
  rw [MvPowerSeries.coeff_map]

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupAction_linearPart_ringHom : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (OE : Type) [CommRing OE] (act : Geo.Tor.Germ.OAct OE F) (S : Type) [CommRing S] (β : R →+* S), ∃ ρ : OE →+* Matrix (Fin d) (Fin d) S, ∀ a, ρ a = linPart (actMap β act a) ∧ ρ a = (lin (act.act a)).map β := by
  first | exact @GlobalTheory.ChF.linPart_act_ringHom | exact GlobalTheory.ChF.linPart_act_ringHom | (intros; apply GlobalTheory.ChF.linPart_act_ringHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSeriesEqOfEvalAtNilpotentPointsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSeriesEqOfEvalAtNilpotentPointsEq
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private def lowZero {A κ : Type} [CommRing A] (e : κ →₀ ℕ) : Ideal (MvPowerSeries κ A) where
  carrier := {g | ∀ e' ≤ e, MvPowerSeries.coeff e' g = 0}
  add_mem' {a b} ha hb e' h := by rw [map_add (f := _), ha e' h, hb e' h, add_zero]
  zero_mem' e' _ := map_zero _
  smul_mem' c x hx e' h := by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2 (le_trans (le_of_le_of_eq le_add_self (Finset.HasAntidiagonal.mem_antidiagonal.1 hp)) h), mul_zero]

private theorem coeff_box {A κ : Type} [CommRing A] [Fintype κ] [DecidableEq κ] (N : ℕ) (c : (κ →₀ ℕ) → A)
    (e : κ →₀ ℕ) (he : ∀ i, e i < N) :
    MvPowerSeries.coeff e (∑ b : κ → Fin N, MvPowerSeries.C (c (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
      ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ (b i : ℕ)) = c e := by
  have hm : ∀ b : κ → ℕ, ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ b i =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm b) 1 := fun b => by
    rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  have he' : (Finsupp.equivFunOnFinite.symm fun i => ((⟨e i, he i⟩ : Fin N) : ℕ)) = e := by
    ext i; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single (fun i => (⟨e i, he i⟩ : Fin N))]
  · rw [hm, MvPowerSeries.coeff_C_mul, he', MvPowerSeries.coeff_monomial_same, _root_.mul_one]
  · intro b _ hb
    rw [hm, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial_ne, mul_zero]
    intro h
    exact hb (funext fun i => Fin.ext (by simp [h]))
  · simp

theorem eq_of_nv_eq : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (n d : ℕ) (f f' : PS R n d), (∀ (S : Type) [CommRing S] [Algebra R S] (k : ℕ), Kills I k S → (IsLocalRing R → I ≠ ⊤ → IsLocalRing S ∧ IsLocalHom (algebraMap R S)) → ∀ a : Fin n → Fin d → S, (∀ i j, IsNilpotent (a i j)) → nv (algebraMap R S) f a = nv (algebraMap R S) f' a) → f = f' := by
  intro R _ I hI n d f f' H
  ext e
  rw [← sub_eq_zero]
  refine hI.haus _ fun k => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  let A := R ⧸ I ^ (k + 1)
  let J : Ideal (MvPowerSeries (Fin n × Fin d) A) := lowZero e
  let N : ℕ := (∑ i, e i) + 1
  have he : ∀ i, e i < N := fun i =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have halg : ∀ t : R, algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J) t =
      Ideal.Quotient.mk J (MvPowerSeries.C (Ideal.Quotient.mk (I ^ (k + 1)) t)) := fun t => by
    rw [← Ideal.Quotient.mk_algebraMap, MvPowerSeries.algebraMap_apply]; rfl
  have hN : ∀ q : Fin n × Fin d, (Ideal.Quotient.mk J (MvPowerSeries.X q)) ^ N = 0 := fun q => by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    intro e' h
    exact (MvPowerSeries.X_pow_dvd_iff.1 dvd_rfl) e' (lt_of_le_of_lt (h q) (he q))
  have hv : ∀ g : PS R n d, nv (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)) g
      (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) =
      Ideal.Quotient.mk J (∑ b : Fin n × Fin d → Fin N, MvPowerSeries.C ((fun x => Ideal.Quotient.mk (I ^ (k + 1))
        (MvPowerSeries.coeff x g)) (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
        ∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n × Fin d) A) ^ (b i : ℕ)) := fun g => by
    letI := (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)).toAlgebra
    refine (evBasic_nEval_eq_tEval g (fun q : Fin n × Fin d => Ideal.Quotient.mk J (MvPowerSeries.X q)) N hN).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [tEval, map_sum, map_mul, map_prod, map_pow]
    exact Finset.sum_congr rfl fun b _ => congrArg (· * _) (halg _)
  have h := H (MvPowerSeries (Fin n × Fin d) A ⧸ J) k (fun t ht => by
      rw [halg, Ideal.Quotient.eq_zero_iff_mem.2 ht, map_zero, map_zero]) (fun hR hne => ?_)
    (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) (fun i j => ⟨N, hN (i, j)⟩)
  · rw [hv, hv, Ideal.Quotient.eq] at h
    have h2 := h e le_rfl
    rw [map_sub, sub_eq_zero] at h2
    exact Ideal.Quotient.eq.1 (((coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f)) e he).symm.trans h2).trans (coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f')) e he))
  · have hA : I ^ (k + 1) ≠ ⊤ := fun h => hne (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero k)))
    haveI : Nontrivial A := Ideal.Quotient.nontrivial_iff.2 hA
    haveI : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hJ : J ≠ ⊤ := fun h => by
      have : (1 : MvPowerSeries (Fin n × Fin d) A) ∈ J := h ▸ Submodule.mem_top
      have := this 0 zero_le
      simp at this
    haveI : Nontrivial (MvPowerSeries (Fin n × Fin d) A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
    refine ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, ⟨fun t ht => ?_⟩⟩
    rw [halg] at ht
    have h1 := (IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).map_nonunit _ ht
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at h1
    exact (IsLocalHom.of_surjective (Ideal.Quotient.mk (I ^ (k + 1))) Ideal.Quotient.mk_surjective).map_nonunit _ h1

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSeriesEqOfEvalAtNilpotentPointsEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (n d : ℕ) (f f' : PS R n d), (∀ (S : Type) [CommRing S] [Algebra R S] (k : ℕ), Kills I k S → (IsLocalRing R → I ≠ ⊤ → IsLocalRing S ∧ IsLocalHom (algebraMap R S)) → ∀ a : Fin n → Fin d → S, (∀ i j, IsNilpotent (a i j)) → nv (algebraMap R S) f a = nv (algebraMap R S) f' a) → f = f' := by
  first | exact @GlobalTheory.ChF.eq_of_nv_eq | exact GlobalTheory.ChF.eq_of_nv_eq | (intros; apply GlobalTheory.ChF.eq_of_nv_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.QRelExistsUniqueMulNat
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

private theorem mul_left_fst {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) {t : Z ⟶ S'} {r : Z ⟶ S}
    (x y : Over.mk t ⟶ (Over.pullback f).obj G) (x₀ y₀ : Over.mk r ⟶ G)
    (hx : x₀.left = x.left ≫ pullback.fst G.hom f) (hy : y₀.left = y.left ≫ pullback.fst G.hom f) :
    (x₀ * y₀).left = (x * y).left ≫ pullback.fst G.hom f := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk t ⟶ (Over.pullback f).obj (G ⊗ G) :=
    lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G
  have z₁ : z ≫ (Over.pullback f).map (fst G G) = x := by simp [z]
  have z₂ : z ≫ (Over.pullback f).map (snd G G) = y := by simp [z]
  have hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left
      rw [lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]
    · show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left
      rw [lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]
  have hxy : x * y = z ≫ (Over.pullback f).map μ[G] := by
    rw [Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]
  rw [hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]
  rfl

private theorem mono_thick (R : Type) [CommRing R] (I : Ideal R) (k : ℕ) : Mono (Out.thick R I k) := by
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem qRel_existsUnique_mul_nat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G), (∀ (S : Type) [CommRing S] [Algebra R S], Kills I k S → (∀ z, ∃! y, QRel c S z y) ∧ ∀ z z' y y', QRel c S z y → QRel c S z' y' → QRel c S (z * z') (y * y')) ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') z y, QRel c S z y → QRel c S' (spMap φ ≫ z) (spMap φ ≫ y) := by
  intro R _ _ I D k G _ _ c
  have hm := mono_thick R I k
  have hf : Mono (pullback.fst G.hom (Out.thick R I k)) := inferInstance
  refine ⟨fun S _ _ hS => ?_, ?_⟩
  · let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
    have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    have hw : ∀ (z : sp (R₀ := R) S ⟶ G) (w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left),
        w ≫ (Out.fstG I k G).left = z.left → w ≫ (Out.thickObj R I k G).hom = t := by
      intro z w h
      rw [← cancel_mono (Out.thick R I k), ht]
      have h1 : (Out.thickObj R I k G).hom ≫ Out.thick R I k = (Out.fstG I k G).left ≫ G.hom :=
        (pullback.condition (f := G.hom) (g := Out.thick R I k)).symm
      rw [Category.assoc, h1, ← Category.assoc, h]
      exact Over.w z
    refine ⟨fun z => ?_, ?_⟩
    · let w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left :=
        pullback.lift z.left t ((Over.w z).trans ht.symm)
      have h1 : w ≫ (Out.fstG I k G).left = z.left := pullback.lift_fst _ _ _
      have h2 : (w ≫ c.pG.left) ≫ D.P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
        have h3 : c.pG.left ≫ D.P.A.hom = (Out.thickObj R I k G).hom ≫ Out.thick R I k := Over.w c.pG
        rw [Category.assoc, h3, ← Category.assoc, hw z w h1, ht]
      refine ⟨Over.homMk (w ≫ c.pG.left) h2, ⟨w, h1, rfl⟩, ?_⟩
      rintro y ⟨w', a, b⟩
      have e : w' = w := (cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (a.trans h1.symm)
      apply Over.OverMorphism.ext
      rw [← b, e]
      rfl
    · rintro z z' y y' ⟨w, a, b⟩ ⟨w', a', b'⟩
      have := c.q_hom
      let x : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w (hw z w a)
      let x' : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w' (hw z' w' a')
      refine ⟨(x * x').left, (mul_left_fst G (Out.thick R I k) x x' z z' a.symm a'.symm).symm, ?_⟩
      have e := mul_left_fst D.P.A (Out.thick R I k) (x ≫ c.q) (x' ≫ c.q) y y'
        (b.symm.trans (Category.assoc _ _ _).symm) (b'.symm.trans (Category.assoc _ _ _).symm)
      rw [← MonObj.mul_comp] at e
      exact ((Category.assoc _ _ _).symm.trans e.symm)
  · rintro S _ _ S' _ _ φ z y ⟨w, a, b⟩
    refine ⟨(spMap φ).left ≫ w, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) a)
    · exact (Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) b)

end GlobalTheory.ChF
end
