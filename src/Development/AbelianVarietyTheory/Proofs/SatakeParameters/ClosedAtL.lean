module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedOfCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeLayerCoverBasisModPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverExists
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

theorem cover_exists : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l)), Continuous r → Formalism.MainNotions.N.IsSSRep r → ∀ Cl : Set (Γ →* GL (Fin a) (Om l)), (∀ ρ ∈ Cl, Continuous ρ) → LinApprox r Cl → Nonempty (Cover L₀ r Cl) := by
  intro l _ Γ _ _ _ _ a L₀ r hr hss Cl hCl hap
  classical
  obtain ⟨d, ρ, b, e, hρ, hreads, hind, hbr⟩ := GlobalTheory.T.exists_padicInt_span_image_lattice_regular l Γ a r hr
  obtain ⟨c, hc⟩ := GlobalTheory.T.small_traces_dvd_span_image l Γ a r hr hss
  obtain ⟨K, hK⟩ := traceL l a d b
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hch : ∀ ρ' : Γ →* GL (Fin a) (Om l), ∃ (L : FinExt l) (t : Finset (Matrix (Fin a) (Fin a) (Om l))), Continuous ρ' →
      (L₀.1 ≤ L.1 ∧ (∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) ∧ (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧
        (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧
        (∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c' y) • y = 1) ∧
        ∀ g, ∀ x ∈ t, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t, zOm l (c' y) • y) := by
    intro ρ'
    by_cases h : Continuous ρ'
    · obtain ⟨L, hLf, hL⟩ := GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep l Γ a ρ' h
      haveI := hLf
      haveI := L₀.2
      let L' : FinExt l := ⟨L ⊔ L₀.1, inferInstance⟩
      have hL' : ∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L'.1 := fun g i j =>
        (le_sup_left : L ≤ L ⊔ L₀.1) (hL g i j)
      obtain ⟨t, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_stable_spanning_finset_matrices l Γ a ρ' L' h hL'
      exact ⟨L', t, fun _ => ⟨le_sup_right, hL', h1, h2, h3, h4⟩⟩
    · exact ⟨L₀, ∅, fun h' => absurd h' h⟩
  choose Lf tf htf using hch

  have hap' : ∀ n : ℕ, ∃ (s : Finset (Γ →* GL (Fin a) (Om l))) (cc : (Γ →* GL (Fin a) (Om l)) → Om l),
      (s : Set (Γ →* GL (Fin a) (Om l))) ⊆ Cl ∧ ∀ g, ‖trc r g - ∑ ρ' ∈ s, cc ρ' * trc ρ' g‖ ≤ ((l : ℝ)⁻¹) ^ (n + K + c) :=
    fun n => hap _ (by positivity)
  choose s cc hsCl hscc using hap'
  let U : ℕ → Finset (Γ →* GL (Fin a) (Om l)) := fun n => (Finset.range (n + 1)).biUnion s
  have hUmono : ∀ n, U n ⊆ U (n + 1) := fun n =>
    Finset.biUnion_subset_biUnion_of_subset_left _ (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
  have hsU : ∀ n, s n ⊆ U n := fun n => Finset.subset_biUnion_of_mem s (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hUCl : ∀ n, ∀ ρ' ∈ U n, ρ' ∈ Cl := by
    intro n ρ' h
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
    exact hsCl j hj
  let m : ℕ → ℕ := fun n => (U n).card
  let ρs : ∀ n, Fin (m n) → (Γ →* GL (Fin a) (Om l)) := fun n k => ((U n).equivFin.symm k).1
  have hρsU : ∀ n k, ρs n k ∈ U n := fun n k => ((U n).equivFin.symm k).2
  have hρsC : ∀ n k, Continuous (ρs n k) := fun n k => hCl _ (hUCl n _ (hρsU n k))
  let cs : ∀ n, Fin (m n) → Om l := fun n k => if ρs n k ∈ s n then cc n (ρs n k) else 0
  have hcs : ∀ n g, ∑ k, cs n k * trc (ρs n k) g = ∑ ρ' ∈ s n, cc n ρ' * trc ρ' g := by
    intro n g
    have e1 : ∑ k, cs n k * trc (ρs n k) g = ∑ x : (U n), (if x.1 ∈ s n then cc n x.1 else 0) * trc x.1 g :=
      Fintype.sum_equiv (U n).equivFin.symm _ _ (fun k => rfl)
    rw [e1, Finset.sum_coe_sort (U n) (fun x => (if x ∈ s n then cc n x else 0) * trc x g)]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsU n)]
  have hK' : ∀ n, ∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ (n + K) • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n w
    rw [Matrix.trace_smul, smul_eq_mul, norm_mul, norm_pow, norm_l]
    calc ((l : ℝ)⁻¹) ^ (n + K) * ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + K) * (l : ℝ) ^ K :=
          mul_le_mul_of_nonneg_left (hK w) (by positivity)
      _ = ((l : ℝ) ^ n)⁻¹ := by
          rw [pow_add, inv_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  have hlay : ∀ n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin (m n) → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (Lf (ρs n k)).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin (m n) → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (Lf (ρs n k)).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs n k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ latT (ρs n) (fun k => tf (ρs n k)) M) ∧ (∀ x ∈ latT (ρs n) (fun k => tf (ρs n k)) M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ Carries r b (ρs n) (fun k => tf (ρs n k)) M bb P (n + K) ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs n k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n
    exact GlobalTheory.T.exists_lattice_layer_cover_basis_mod_pow l Γ a r d ρ b e hreads hind hbr c hc n (n + K) (by omega) (hK' n) (m n) (ρs n)
      (fun k => Lf (ρs n k)) (fun k => tf (ρs n k)) (hρsC n) (fun k => (htf _ (hρsC n k)).2.1)
      (fun k => (htf _ (hρsC n k)).2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.1)
      (fun k => (htf _ (hρsC n k)).2.2.2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.2.2) (cs n)
      (fun g => by rw [hcs n g]; exact hscc n g)
  choose M₀ hM₀ using hlay
  let M : ℕ → ℕ := fun n => ∑ j ∈ Finset.range (n + 1), M₀ j
  have hMle : ∀ n, M₀ n ≤ M n := fun n =>
    Finset.single_le_sum (f := M₀) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hMmono : ∀ n, M n ≤ M (n + 1) := fun n => by
    simp only [M]
    rw [Finset.sum_range_succ _ (n + 1)]
    exact Nat.le_add_right _ _
  have hL := fun n => hM₀ n (M n) (hMle n)
  choose d' ρ' bb e' P hcont hbbL hind' hspan' hreads' hmem hcoord hcar honto hunit htr using hL
  let ι : ∀ n, Fin (m n) → Fin (m (n + 1)) := fun n k =>
    (U (n + 1)).equivFin ⟨((U n).equivFin.symm k).1, hUmono n ((U n).equivFin.symm k).2⟩
  have hι : ∀ n k, ρs (n + 1) (ι n k) = ρs n k := by
    intro n k
    simp [ρs, ι]
  have htrans : ∀ n, ∃ f : Matrix (Fin (d' n)) (Fin (d' (n + 1))) ℤ_[l], (∀ g, f * ((ρ' (n + 1) g : GL (Fin (d' (n + 1))) ℤ_[l]) : Matrix (Fin (d' (n + 1))) (Fin (d' (n + 1))) ℤ_[l]) = ((ρ' n g : GL (Fin (d' n)) ℤ_[l]) : Matrix (Fin (d' n)) (Fin (d' n)) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P n * f - P (n + 1)) i j := by
    intro n
    exact GlobalTheory.T.exists_equivariant_transition_matrix_cover l Γ a r d b hind (m n) (m (n + 1)) (ρs n) (ρs (n + 1)) (ι n) (hι n)
      (fun k => tf (ρs n k)) (fun k => tf (ρs (n + 1) k)) (fun k => by rw [hι n k]) (M n) (M (n + 1)) (hMmono n)
      (d' n) (d' (n + 1)) (ρ' n) (ρ' (n + 1)) (bb n) (bb (n + 1)) (e' n) (e' (n + 1)) (hind' n) (hreads' n)
      (hreads' (n + 1)) (hmem (n + 1)) (hcoord n) (P n) (P (n + 1)) n (n + K) (n + 1 + K) (by omega) (by omega)
      (hcar n) (hcar (n + 1))
  choose f hfe hfP using htrans
  let tw : Tower ρ :=
    { d' := d', ρ' := ρ', Pi := P, onto := honto, f := f, f_equi := hfe, f_Pi := hfP }
  let lay : ∀ n, Layer L₀ Cl (tw.ρ' n) := fun n =>
    { m := m n, rep := ρs n, mem := fun k => hUCl n _ (hρsU n k), L := fun k => Lf (ρs n k),
      le := fun k => (htf _ (hρsC n k)).1, rep_mem := fun k => (htf _ (hρsC n k)).2.1, b := bb n,
      b_mem := hbbL n, indep := hind' n, span := hspan' n, e := e' n, reads := hreads' n, c := cs n }
  exact ⟨{ d := d, ρ := ρ, cont := hρ, b := b, e := e, reads := hreads, tw := tw, cont' := hcont, lay := lay,
            unit := hunit, trace := htr }⟩

end GlobalTheory.TraceConjugationCover

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPull
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

def Layer.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {a d' : ℕ} {L₀ : FinExt l}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} {ρ' : Γ →* GL (Fin d') ℤ_[l]} (Y : Layer L₀ Cl ρ') :
    Layer L₀ ((fun ρ => ρ.comp j) '' Cl) (ρ'.comp j) where
  m := Y.m
  rep k := (Y.rep k).comp j
  mem k := ⟨Y.rep k, Y.mem k, rfl⟩
  L := Y.L
  le := Y.le
  rep_mem k g := Y.rep_mem k (j g)
  b := Y.b
  b_mem := Y.b_mem
  indep := Y.indep
  span := Y.span
  e := Y.e
  reads k := ⟨fun g => (Y.reads k).equi (j g), (Y.reads k).one⟩
  c := Y.c

def Tower.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [Group Δ] (j : Δ →* Γ) {d : ℕ}
    {ρ : Γ →* GL (Fin d) ℤ_[l]} (T : Tower ρ) : Tower (ρ.comp j) where
  d' := T.d'
  ρ' n := (T.ρ' n).comp j
  Pi := T.Pi
  onto n := ⟨fun g => (T.onto n).equi (j g), (T.onto n).surj⟩
  f := T.f
  f_equi n g := T.f_equi n (j g)
  f_Pi := T.f_Pi

def Cover.pull {l : ℕ} [Fact l.Prime] {Γ Δ : Type} [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ]
    (j : Δ →* Γ) (hj : Continuous j) {a : ℕ} {L₀ : FinExt l} {r : Γ →* GL (Fin a) (Om l)}
    {Cl : Set (Γ →* GL (Fin a) (Om l))} (C : Cover L₀ r Cl) :
    Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl) where
  d := C.d
  ρ := C.ρ.comp j
  cont := C.cont.comp hj
  b := C.b
  e := C.e
  reads := ⟨fun g => C.reads.equi (j g), C.reads.one⟩
  tw := C.tw.pull j
  cont' n := (C.cont' n).comp hj
  lay n := (C.lay n).pull j
  unit := C.unit
  trace := C.trace

theorem cover_pull : ∀ (l : ℕ) [Fact l.Prime] (Γ Δ : Type) [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ] (j : Δ →* Γ), Continuous j → ∀ (a : ℕ) (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))), Cover L₀ r Cl → Nonempty (Cover L₀ (r.comp j) ((fun ρ => ρ.comp j) '' Cl)) :=
  by
  intro _ _ _ _ _ _ _ _ j hj _ _ _ _ C
  exact ⟨C.pull j hj⟩

end GlobalTheory.BKLim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstOfCoordRev
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open TensorProduct Module GlobalTheory.CoeffExt

namespace GlobalTheory.SstModel

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_of_coord_rev [Nonempty ι] (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ') :
    IsSst P ρ := by
  have hm : ∀ x : V' ⊗[ℚ_[l]] Bst P, x ∈ Dst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dst P ρ := fun x => by
    simp only [mem_Dst]
    refine ⟨fun hx i g => by rw [← GlobalTheory.PstExt.tensCoord_stRep P hE, hx g], fun hx g => ?_⟩
    exact (tensCoord E (Bst P)).injective (funext fun i => by rw [GlobalTheory.PstExt.tensCoord_stRep P hE, hx i g])
  let e : ↥(Dst P ρ') ≃ₗ[ℚ_[l]] (ι → ↥(Dst P ρ)) :=
    { toFun := fun x i => ⟨tensCoord E (Bst P) x.1 i, (hm _).1 x.2 i⟩
      invFun := fun y => ⟨(tensCoord E (Bst P)).symm fun i => (y i).1, (hm _).2 fun i => by
        rw [LinearEquiv.apply_symm_apply]; exact (y i).2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
      map_smul' := fun c x => funext fun i =>
        Subtype.ext (congrFun (((tensCoord E (Bst P)).restrictScalars ℚ_[l]).map_smul c x.1) i)
      left_inv := fun x => Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
      right_inv := fun y => funext fun i =>
        Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i) }
  rw [GlobalTheory.AboveL.RepConj.isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, GlobalTheory.AboveL.RepConj.finrank_pi_card,
    GlobalTheory.AboveL.RepConj.finrank_pi_card, mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos h

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_of_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l}
    (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1)
    (h : IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :
    IsSst P (Bw.repE L₁ r₁) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have : Nonempty (Fin (finrank ↥L₁.1 ↥L₂.1)) := ⟨⟨0, finrank_pos⟩⟩
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord_rev P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSst_of_isModel {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {r : ↥Gw →* GL (Fin m) (Om l)}
    {L : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥L.1} (hm : IsModel Bw r L r') (hs : IsSstAt P Bw r) :
    IsSst P (Bw.repE L r') := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := hs
  have l₁ : L₁.1 ≤ (supExt L₁ L).1 := le_sup_left
  have l₂ : L.1 ≤ (supExt L₁ L).1 := le_sup_right
  have e := IsModel.unique Bw r (h₁.enlarge l₁) (hm.enlarge l₂)
  have h3 := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hp
  rw [e] at h3
  exact isSst_of_enlarge P Bw l₂ r' h3

end GlobalTheory.SstModel

namespace GlobalTheory.SstModel

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (LL' : FinExt l) (r' : ↥Gw →* GL (Fin a) ↥LL'.1), IsModel Bw r LL' r' → IsSstAt P Bw r → IsSst P (Bw.repE LL' r') := by
  intro l _ P AI _ E Ω _ _ _ Gw O _ _ _ Bw a r LL' r' hm hs
  exact isSst_of_isModel P hm hs

end GlobalTheory.SstModel

end
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

noncomputable section

namespace GlobalTheory.LimitTop

open Matrix Formalism.WeaklyAdmissibleFiltrations

theorem closedAtL : ClosedAtL := by
  intro E Ω _ _ _ _ _ l _ a ha P AI hT w A hA O _ _ _ Bw hBw J r hr hss C hC hρ
  classical
  obtain ⟨T⟩ := hT

  let jl : ↥(GK Bw.Kw) →* Formalism.ConjugateSelfDual.G E Ω := (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom
  have hjl : Continuous jl := continuous_subtype_val.comp Bw.e_symm_cont

  let jE : E →+* ↥Bw.Kw.1 := (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E
  let J' : (↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ := fun τ'' => J (τ''.toRingHom.comp jE)
  obtain ⟨Cv⟩ := GlobalTheory.TraceConjugationCover.cover_exists l (Formalism.ConjugateSelfDual.G E Ω) a Bw.LL r hr hss C (fun ρ hm => (hρ ρ hm).1) hC
  obtain ⟨Cv'⟩ := GlobalTheory.BKLim.cover_pull l (Formalism.ConjugateSelfDual.G E Ω) ↥(GK Bw.Kw) jl hjl a Bw.LL r C Cv

  have tr : ∀ (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 →
      (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = ((ρ.comp jl) g).val i k) →
      IsModel Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r'.comp Bw.e.toMonoidHom) ∧
        Bw.repE L (r'.comp Bw.e.toMonoidHom) = R := by
    intro ρ L r' R hle hR he
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · ext g i k
      have := he (Bw.e g) i k
      simpa [jl, mapRep] using this
    · refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
      rw [hR]
      simp [LocBridge.repE, Matrix.toLin'_apply]

  have hCl : ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C, ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) →
      IsSst P R ∧ ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD Bw.Kw) R τ n = ((J' (L.1.val.comp τ)).count n : ℤ) := by
    rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
    obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
    refine ⟨hrep ▸ GlobalTheory.SstModel.main l P AI ⟨T⟩ E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O Bw a _ L _ hmod (hρ ρ hm).2.1, fun τ n => ?_⟩
    have hi : IsInduced Bw ((L.1.val.comp τ).toRingHom.comp jE) τ := fun x => rfl
    have := IsJumpsAt.count_eq P hmod hi ((hρ ρ hm).2.2 _ L τ hi) n
    rw [← hrep]
    exact this.symm
  have hcr : (∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) → ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C,
      ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)),
      Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) → IsCrys (P.PD Bw.Kw) R := by
    intro hc
    rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
    obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
    rw [← hrep]
    exact (hmod.isCrysAt_iff P).1 (hc ρ hm)

  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  have model : ∀ L₀ : FinExt l, ∃ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), L₀.1 ≤ L.1 ∧ Bw.LL.1 ≤ L.1 ∧
      mapRep (algebraMap ↥L.1 (Om l)) r₁ = r := by
    intro L₀
    haveI := L₀.2
    haveI := Bw.LL.2
    obtain ⟨L, hL, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a r hcont
      ⟨L₀.1 ⊔ Bw.LL.1, IntermediateField.finiteDimensional_sup _ _⟩
    obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont L hmem
    exact ⟨L, r₁, le_sup_left.trans hL, le_sup_right.trans hL, hr₁⟩

  have top : ∀ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), Bw.LL.1 ≤ L.1 → mapRep (algebraMap ↥L.1 (Om l)) r₁ = r →
      IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
      Bw.IsdRE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
      (∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ),
        Bw.multE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ n = ((J' (L.1.val.comp τ)).count n : ℤ)) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) →
        Bw.IsCrysE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    intro L r₁ hle hr₁
    have hmod : IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
      ⟨hle, by rw [← hr₁]; rfl⟩
    obtain ⟨hdr, hmu, hcy⟩ := GlobalTheory.CovClose.closed_of_cover l Bw.Kw Bw.LL P AI T a ha Bw.LL_split (r.comp jl) _ Cv' J' hCl L
      (r₁.comp jl) (Bw.repE L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) hle
      (fun g v => by simp [LocBridge.repE, jl, Matrix.toLin'_apply]) (fun g i k => by rw [← hr₁]; rfl)
    refine ⟨hmod, ?_, hmu, fun hc => hcy (hcr hc)⟩
    have h := hdr
    unfold Formalism.MainNotions.N.IsDR at h
    rw [Module.finrank_fin_fun] at h
    exact h
  refine ⟨⟨?_, fun τ LL' τ' hi => ?_⟩, fun hc => ?_⟩
  · obtain ⟨L, r₁, -, hle, hr₁⟩ := model Bw.LL
    obtain ⟨hmod, hdr, -, -⟩ := top L r₁ hle hr₁
    exact ⟨L, _, hmod, hdr⟩
  · obtain ⟨L, r₁, hL', hle, hr₁⟩ := model LL'
    obtain ⟨hmod, hdr, hmu, -⟩ := top L r₁ hle hr₁
    let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1 := (IntermediateField.inclusion hL').comp τ'
    have hi' : IsInduced Bw τ τ'' := fun x => hi x
    have hτ : (L.1.val.comp τ'').toRingHom.comp jE = τ := RingHom.ext fun x => (hi x).symm
    refine ⟨L, _, hmod, hdr, τ'', hi', fun n => ?_⟩
    rw [hmu τ'' n]
    show ((J τ).count n : ℤ) = ((J ((L.1.val.comp τ'').toRingHom.comp jE)).count n : ℤ)
    rw [hτ]
  · obtain ⟨L, r₁, -, hle, hr₁⟩ := model Bw.LL
    obtain ⟨hmod, -, -, hcy⟩ := top L r₁ hle hr₁
    exact ⟨L, _, hmod, hcy hc⟩

end GlobalTheory.LimitTop
