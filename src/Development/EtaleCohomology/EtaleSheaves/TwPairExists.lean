module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
public import Development.EtaleCohomology.CohomologicalPurity.LeafAWCutTw
public import Development.EtaleCohomology.TateTwists.TPaTensUnivPf
public import Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeTwoValueOfRootsKum
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorRestrictionAndRootChangeH
public import Development.EtaleCohomology.TateTwists.EtaleComplexAcyclicIffLocalExactness
public import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupExistsOfComponents

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.TwpairZcFunPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

section
variable {R : Type} [CommRing R]

lemma zc_pull_mk {K L I : Cx R} (f : K ⟶ L) (n : ℤ) (b : Cocycle L I n) :
    cpull f I n (CohomologyClass.mk b) =
      CohomologyClass.mk (Cocycle.mk ((Cochain.ofHom f).comp b.1 (zero_add n)) (n + 1) rfl
        (by rw [δ_ofHom_comp, Cocycle.δ_eq_zero, Cochain.comp_zero])) := by
  rw [cpre_mk]; congr 1

lemma zc_push_mk {K I J : Cx R} (g : I ⟶ J) (n : ℤ) (a : Cocycle K I n) :
    cpush K g n (CohomologyClass.mk a) =
      CohomologyClass.mk (Cocycle.mk (a.1.comp (Cochain.ofHom g) (add_zero n)) (n + 1) rfl
        (by rw [δ_comp_ofHom, Cocycle.δ_eq_zero, Cochain.zero_comp])) := by
  rw [cpost_mk]; congr 1

end

theorem twpair_zc_fun_of : twpair_zc_fun := by
  intro R _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    constructor
    · rw [zc_pull_mk]; congr 1; apply Cocycle.ext; simp [Cochain.id_comp]
    · rw [zc_push_mk]; congr 1; apply Cocycle.ext; simp [Cochain.comp_id]
  · intro K L M f g I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_pull_mk, zc_pull_mk, zc_pull_mk]; congr 1; apply Cocycle.ext
    simp [Cochain.ofHom_comp]
  · intro K I J M f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_push_mk, zc_push_mk]
    congr 1
  · intro K L I J f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_pull_mk, zc_pull_mk, zc_push_mk]; congr 1; apply Cocycle.ext
    simp
  · intro K L f g ⟨ho⟩ I n
    obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g ho
    constructor
    · ext x
      obtain ⟨b, rfl⟩ := x.mk_surjective
      rw [zc_pull_mk, zc_pull_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • z.comp b.1 (by omega), ?_⟩
      have hb : δ n (n + 1) (b : Cochain L I n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp only [hb, Cochain.comp_zero, zero_add, smul_smul, Int.units_mul_self, one_smul, hz',
        Cochain.sub_comp]
      rfl
    · ext x
      obtain ⟨a, rfl⟩ := x.mk_surjective
      rw [zc_push_mk, zc_push_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨a.1.comp z (by omega), ?_⟩
      have ha : δ n (n + 1) (a : Cochain I K n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega)]
      simp only [ha, Cochain.zero_comp, smul_zero, add_zero, hz', Cochain.comp_sub]
      rfl

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.SubdivisionComposition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SubdivisionComposition

lemma subint_comp (N j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l) :
    SimplexCategory.subinterval j' l' h' ≫ SimplexCategory.subinterval j l h =
      SimplexCategory.subinterval (n := N) (j + j') l' (by omega) := by
  ext i
  change ((i : ℕ) + j' + j) = (i : ℕ) + (j + j')
  omega

lemma subint_id (N : ℕ) :
    SimplexCategory.subinterval (n := N) 0 N (by omega) = 𝟙 _ := by
  ext i
  simp [SimplexCategory.subinterval]

lemma along_comp {E : Spc} {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) :
    (x.along a).along b = x.along (b ≫ a) := by
  simp only [Sx.along, op_comp, Functor.map_comp, NatTrans.comp_app, types_comp_apply]

end LateralTheory.EtaleFoundations.SubdivisionComposition

open LateralTheory.EtaleFoundations.SubdivisionComposition in
theorem LateralTheory.EtaleFoundations.simplicial_subinterval_of_subinterval_along_etale : LateralTheory.EtaleFoundations.EtaleSimplexSubfaceComposition := by
  intro E U N x
  have hsa : ∀ (j l : ℕ) (h : j + l ≤ N), x.sub j l h = x.along (SimplexCategory.subinterval j l h) :=
    fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l j' l' h h'
    change (x.along _).along _ = x.along _
    rw [along_comp, subint_comp]
  · rw [hsa, subint_id]
    simp [Sx.along]
  · intro j l h
    refine ⟨?_, ?_, hsa j l h⟩
    · intro V g
      simp only [Sx.sub, Sx.res]
      have hn := ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x
      simp only [ConcreteCategory.comp_apply] at hn
      exact hn
    · intro E' f
      simp only [Sx.sub, Sx.map]
      have hn := congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)
      simp only [NatTrans.comp_app] at hn
      first
        | (have hm := ConcreteCategory.congr_hom hn x
           simp only [ConcreteCategory.comp_apply] at hm
           first | exact hm | exact hm.symm)
        | exact (congrFun hn x).symm
        | (rw [← types_comp_apply, ← hn]; rfl)
  · intro p r a b
    exact along_comp x a b
end

section -- merged from Development.EtaleCohomology.TateTwists.TTwpairExPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleTateTwistCupPairingExistsAndCupUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
      ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem t_twpair_ex_of (htw : EtaleTateTwistCupPairingExistsAndCupUnique) : t_twpair_ex := by
  intro q _ i j
  exact ⟨twPair q i j, (htw q i j).1⟩

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSteenrodWhitneyAlexanderCompatibilityOfComp
section -- merged from Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations
section -- merged from Development.EtaleCohomology.TateTwists.PrismAlexanderWhitneySwapChainHomotopy
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy : Prop :=
  ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧ ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1)
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

def leaf_acyc : Prop := ∀ (N k : ℕ) (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 →
  ∃ b : Pr N →₀ ℤ, Pr.Deg (k + 2) b ∧ Pr.d N b = c

def leaf_dbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)

def leaf_bdbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0

def leaf_aw : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N)

def leaf_wa : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N)

lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

lemma deg_bd {N k : ℕ} {c : Pr N →₀ ℤ} (hc : Pr.Deg k c) : Pr.Deg k (Pr.bd c) := by
  intro z hz
  unfold Pr.bd at hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have h2 := Finsupp.support_smul hi
  unfold Pr.push at h2
  simp only [Finsupp.lmapDomain_apply] at h2
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h2)
  exact hc w hw

lemma deg_aw (N : ℕ) : Pr.Deg N (Pr.aw N) := by
  intro z hz
  unfold Pr.aw at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (p : ℕ) + (N - p) = N
  omega

lemma deg_wa (N : ℕ) : Pr.Deg N (Pr.wa N) := by
  intro z hz
  unfold Pr.wa at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (N - p) + (p : ℕ) = N
  omega

lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  unfold Pr.bd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, smul_sub]

lemma bd_zero {N : ℕ} : Pr.bd (0 : Pr N →₀ ℤ) = 0 := by
  simpa using bd_sub (0 : Pr N →₀ ℤ) 0

lemma aw_zero_eq : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]

def Good (N : ℕ) (x : Pr N →₀ ℤ) : Prop :=
  Pr.Deg (N + 1) x ∧ Pr.bd (Pr.aw N - Pr.wa N - Pr.d N x) = 0

lemma step (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd) (hAW : leaf_aw) (hWA : leaf_wa)
    (N : ℕ) (x : Pr N →₀ ℤ) (hx : Good N x) :
    ∃ y : Pr (N + 1) →₀ ℤ, Good (N + 1) y ∧ Pr.d (N + 1) y + Pr.bd x = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  set c := Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd x with hcdef
  have hcdeg : Pr.Deg (N + 1) c := deg_sub (deg_sub (deg_aw _) (deg_wa _)) (deg_bd hx.1)
  have hcyc : Pr.d (N + 1) c = 0 := by
    rw [hcdef, map_sub, map_sub, hAW, hWA, hD, ← bd_sub, ← bd_sub]
    exact hx.2
  obtain ⟨b, hbdeg, hb⟩ := hA (N + 1) N c hcdeg hcyc
  refine ⟨b, ⟨hbdeg, ?_⟩, ?_⟩
  · have : Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.d (N + 1) b = Pr.bd x := by
      rw [hb, hcdef]; abel
    rw [this]; exact hB N x
  · rw [hb, hcdef]; abel

lemma good_zero : Good 0 0 := by
  refine ⟨deg_zero, ?_⟩
  rw [aw_zero_eq, map_zero, sub_self, sub_zero, bd_zero]

end LateralTheory.EtaleFoundations.SteenPf

open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd)
    (hAW : leaf_aw) (hWA : leaf_wa) : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  classical
  let seq : ∀ N, {x : Pr N →₀ ℤ // Good N x} := fun N =>
    Nat.rec (motive := fun N => {x : Pr N →₀ ℤ // Good N x}) ⟨0, good_zero⟩
      (fun N x => ⟨Classical.choose (step hA hD hB hAW hWA N x.1 x.2),
        (Classical.choose_spec (step hA hD hB hAW hWA N x.1 x.2)).1⟩) N
  refine ⟨fun N => (seq N).1, fun N => (seq N).2.1, ?_, fun N => ?_⟩
  · show Pr.d 0 0 = _
    rw [map_zero, aw_zero_eq, sub_self]
  · exact (Classical.choose_spec (step hA hD hB hAW hWA N (seq N).1 (seq N).2)).2
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit
section -- merged from Development.EtaleCohomology.TateTwists.PrismBoundaryMapSquareZeroHolds
open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

lemma push_push {N M K : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M)
    (θ' : SimplexCategory.mk M ⟶ SimplexCategory.mk K) (c : Pr N →₀ ℤ) :
    Pr.push θ' (Pr.push θ c) = Pr.push (θ ≫ θ') c := by
  simp only [Pr.push, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  rfl

def inv {N : ℕ} (p : Fin (N + 3) × Fin (N + 2)) : Fin (N + 3) × Fin (N + 2) :=
  if h : (p.2 : ℕ) < p.1 then (p.2.castSucc, p.1.pred (by intro e; rw [e] at h; simp at h))
  else (p.2.succ, p.1.castPred (fun e => by have := congrArg Fin.val e; have := p.2.isLt; simp at this; simp at *; omega))

theorem prism_boundary_map_square_zero_holds : leaf_bdbd := by
  intro N c
  unfold Pr.bd
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, push_push, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_product' (f := fun (i : Fin (N + 3)) (j : Fin (N + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • Pr.push (SimplexCategory.δ j ≫ SimplexCategory.δ i) c)]
  refine Finset.sum_involution (fun p _ => inv p) ?_ ?_ (fun p _ => by simp) ?_
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h
    · have hj : j ≤ i.pred (fun e => by subst e; simp at h) := by
        rw [Fin.le_def, Fin.val_pred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      have hi : (i.pred (fun e => by subst e; simp at h)).succ = i := Fin.succ_pred _ _
      rw [hi] at e
      simp only [Fin.val_castSucc, Fin.val_pred]
      rw [e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨i - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]; ring
    · push Not at h
      have hne : i ≠ Fin.last (N + 2) := fun e => by have := congrArg Fin.val e; have := j.isLt; simp at this; simp at *; omega
      have hj : i.castPred hne ≤ j := by rw [Fin.le_def, Fin.coe_castPred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      rw [Fin.castSucc_castPred] at e
      simp only [Fin.val_succ, Fin.coe_castPred]
      rw [← e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      rw [pow_succ]; ring
  · rintro ⟨i, j⟩ - -
    simp only [inv]
    split_ifs with h <;> intro e <;> simp [Prod.ext_iff, Fin.ext_iff] at e <;> omega
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h h2 h2
    · exfalso; simp at h2; omega
    · simp [Prod.ext_iff, Fin.ext_iff]
    · simp [Prod.ext_iff, Fin.ext_iff]
    · exfalso; simp at h2; omega

end LateralTheory.EtaleFoundations.SteenPf
end

section -- merged from Development.EtaleCohomology.TateTwists.SteenrodPrismChainDifferentialSquaredEqZeroOfEta
open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

lemma push_d₁ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₁ = Pr.d₁ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases p with
  | zero => simp [Pr.d₁]
  | succ p =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Pr.d₁, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

lemma push_d₂ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₂ = Pr.d₂ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases r with
  | zero => simp [Pr.d₂]
  | succ r =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Pr.d₂, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

lemma push_single {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) (n : ℤ) :
    Pr.push θ (Finsupp.single z n) = Finsupp.single ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ n := by
  simp [Pr.push]

lemma d_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c) := by
  have : (Pr.d M).comp (Pr.push θ) = (Pr.push θ).comp (Pr.d N) := by
    refine Finsupp.lhom_ext fun z n => ?_
    simp only [LinearMap.comp_apply, push_single, Pr.d, Finsupp.linearCombination_single, map_smul,
      map_add, push_d₁, push_d₂]
  exact LinearMap.congr_fun this c

theorem steenrod_prism_chain_differential_squared_eq_zero_of_etale : leaf_dbd := by
  intro N c
  unfold Pr.bd
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, d_push]

end LateralTheory.EtaleFoundations.SteenPf
end

open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney (hA : leaf_acyc) (hAW : leaf_aw) (hWA : leaf_wa) :
    LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy :=
  LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations hA steenrod_prism_chain_differential_squared_eq_zero_of_etale prism_boundary_map_square_zero_holds hAW hWA
end

section -- merged from Development.EtaleCohomology.TateTwists.LeafAwPf
open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwPf

abbrev sb {n : ℕ} (j l : ℕ) (h : j + l ≤ n) : SimplexCategory.mk l ⟶ SimplexCategory.mk n :=
  SimplexCategory.subinterval j l h

@[simp] lemma sb_apply {n : ℕ} (j l : ℕ) (h : j + l ≤ n) (i : Fin (l + 1)) :
    (((sb j l h).toOrderHom i : Fin (n + 1)) : ℕ) = i + j := rfl

lemma m_last (p r : ℕ) (h1 : 0 + (p + 1) ≤ p + r + 1) (h2 : 0 + p ≤ p + r + 1) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ sb 0 (p + 1) h1 = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_zero (p r : ℕ) (h1 : p + (r + 1) ≤ p + r + 1) (h2 : (p + 1) + r ≤ p + r + 1) :
    SimplexCategory.δ 0 ≫ sb p (r + 1) h1 = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_lo (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + (p + 1) ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k, by omega⟩ : Fin (p + 2)) ≫ sb 0 (p + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma simplex_subinterval_back_comp_face_within_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : p + r ≤ p + r)
    (h2 : (p + 1) + r ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_hi (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + p ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma simplex_subinterval_back_comp_face_above_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : p + r ≤ p + r)
    (h2 : p + (r + 1) ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k - p, by omega⟩ : Fin (r + 2)) ≫ sb p (r + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

def T (n p r : ℕ) (h : p + r ≤ n) : Pr n := ⟨p, r, sb 0 p (by omega), sb p r h⟩

noncomputable def S (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Finsupp.single (T n x.1 x.2 h) 1 else 0

noncomputable def g1 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Pr.d₁ (T n x.1 x.2 h) else 0

noncomputable def g2 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then (-1 : ℤ) ^ x.1 • Pr.d₂ (T n x.1 x.2 h) else 0

lemma aw_eq (n : ℕ) : Pr.aw n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, S n x := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range (fun k => S n (k, n - k))]
  unfold Pr.aw
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.isLt
  simp only [S]
  rw [dite_eq_left (by omega)]
  rfl

lemma bd_sum {N : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Pr N →₀ ℤ) :
    Pr.bd (∑ x ∈ s, g x) = ∑ x ∈ s, Pr.bd (g x) := by
  unfold Pr.bd
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_comm

lemma d_S (n : ℕ) (x : ℕ × ℕ) : Pr.d n (S n x) = g1 n x + g2 n x := by
  unfold S g1 g2
  split_ifs with h
  · simp only [Pr.d, Finsupp.linearCombination_single, one_smul]
    rfl
  · simp

lemma split_sum {M : Type*} [AddCommMonoid M] (p r : ℕ) (f : Fin (p + r + 2) → M) :
    ∑ k, f k = ∑ i : Fin (p + 1), f ⟨i, by omega⟩ + ∑ j : Fin (r + 1), f ⟨p + 1 + j, by omega⟩ := by
  rw [← (finCongr (by omega : (p + 1) + (r + 1) = p + r + 2)).sum_comp, Fin.sum_univ_add]
  rfl

lemma bd_single (n : ℕ) (z : Pr n) : Pr.bd (Finsupp.single z 1) =
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • Finsupp.single
      (⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ k, z.2.2.2 ≫ SimplexCategory.δ k⟩ : Pr (n + 1)) 1 := by
  unfold Pr.bd
  simp [Pr.push]

lemma key (p r : ℕ) :
    Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) + (-1 : ℤ) ^ p • Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) =
      Pr.bd (Finsupp.single (T (p + r) p r le_rfl) 1) := by
  have e1 : Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) = ∑ i : Fin (p + 2),
      Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (i : ℕ)) := rfl
  have e2 : Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) = ∑ j : Fin (r + 2),
      Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (j : ℕ)) := rfl
  rw [e1, e2, bd_single, split_sum, Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := r + 1)]
  have hlo : ∀ i : Fin (p + 1),
      (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      Finsupp.single (⟨p, r, SimplexCategory.δ i.castSucc ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.castSucc i : Fin (p + 2)) : ℕ)) := by
    intro i
    have hi := i.isLt
    simp only [T]
    rw [m_lo p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega), simplex_subinterval_back_comp_face_within_front p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega),
      Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  have hhi : ∀ j : Fin (r + 1),
      (-1 : ℤ) ^ (p + 1 + (j : ℕ)) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j.succ ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.succ j : Fin (r + 2)) : ℕ)) := by
    intro j
    have hj := j.isLt
    simp only [T]
    rw [m_hi p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega), simplex_subinterval_back_comp_face_above_front p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega),
      Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]
    have hf : (⟨p + 1 + (j : ℕ) - p, by omega⟩ : Fin (r + 2)) = j.succ := by
      ext; simp; omega
    rw [hf, Fin.val_succ]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun i _ => hlo i), Finset.sum_congr rfl (fun j _ => hhi j), ← Finset.smul_sum,
    m_last p r (by omega) (by omega), m_zero p r (by omega) (by omega), smul_add]
  have hc : Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ)) +
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((0 : Fin (r + 2)) : ℕ)) = 0 := by
    rw [Finsupp.smul_single, ← Finsupp.single_add]
    simp [pow_succ]
  apply eq_of_sub_eq_zero
  rw [← hc]
  abel

theorem leaf_aw_of : LateralTheory.EtaleFoundations.SteenPf.leaf_aw := by
  intro N
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aw_eq, aw_eq, map_sum, bd_sum]
  simp only [d_S]
  rw [Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  have z1 : g1 (N + 1) (0, N + 1) = 0 := by
    unfold g1; rw [dite_eq_left (by simp)]; rfl
  have z2 : g2 (N + 1) (N + 1, 0) = 0 := by
    unfold g2; rw [dite_eq_left (by simp)]
    show (-1 : ℤ) ^ (N + 1) • (0 : Pr (N + 1) →₀ ℤ) = 0
    exact smul_zero _
  rw [z1, z2, zero_add, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨p, r⟩ := x
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  simp only at hx
  subst hx
  unfold g1 g2 S
  rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega), dite_eq_left (by simp)]
  exact key p r

end LateralTheory.EtaleFoundations.AwPf
end

section -- merged from Development.EtaleCohomology.TateTwists.LeafAcycPf
open CategoryTheory GlobalTheory.EtC

noncomputable section

namespace LateralTheory.EtaleFoundations.AcycPf

def cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨fun i => Fin.cases 0 (fun j => a.toOrderHom j) i, by
    intro i j h
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (by simp)
      | succ j => simpa using a.toOrderHom.monotone (Fin.succ_le_succ_iff.1 h)⟩

def v0 {N : ℕ} : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

lemma δ0_cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 0 ≫ cone a = a := by
  ext j
  simp [SimplexCategory.δ, cone]

lemma δsucc_cone {p N : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (i : Fin (p + 2)) :
    SimplexCategory.δ i.succ ≫ cone a = cone (SimplexCategory.δ i ≫ a) := by
  ext j
  induction j using Fin.cases with
  | zero => simp [SimplexCategory.δ, cone]
  | succ j => simp [SimplexCategory.δ, cone, Fin.succ_succAbove_succ]

lemma δ1_cone {N : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 1 ≫ cone a = v0 := by
  ext j
  fin_cases j
  simp [SimplexCategory.δ, cone, v0]
  rfl

abbrev X {N : ℕ} (p r : ℕ) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) : Pr N →₀ ℤ :=
  Finsupp.single (⟨p, r, a, b⟩ : Pr N) 1

def Hg {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  X (z.1 + 1) z.2.1 (cone z.2.2.1) z.2.2.2 + if z.1 = 0 then X 0 (z.2.1 + 1) v0 (cone z.2.2.2) else 0

def H (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ Hg

lemma d_X {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d N (X p r a b) = Pr.d₁ (⟨p, r, a, b⟩ : Pr N) + (-1 : ℤ) ^ p • Pr.d₂ (⟨p, r, a, b⟩ : Pr N) := by
  simp [Pr.d, X]

lemma H_X {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    H N (X p r a b) = Hg (⟨p, r, a, b⟩ : Pr N) := by
  simp [H, X]

lemma Hg_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Hg (⟨0, r, a, b⟩ : Pr N) = X 1 r (cone a) b + X 0 (r + 1) v0 (cone b) := by
  simp [Hg]

lemma Hg_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Hg (⟨p + 1, r, a, b⟩ : Pr N) = X (p + 2) r (cone a) b := by
  simp [Hg]

lemma diffOne_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

lemma simplex_pair_second_face_of_vertex_eq_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

lemma simplex_pair_first_face_succ_alternating_sum {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • X p r (SimplexCategory.δ i ≫ a) b := by
  simp [Pr.d₁, X]

lemma simplex_pair_second_face_succ_alternating_sum {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) = ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • X p r a (SimplexCategory.δ i ≫ b) := by
  simp [Pr.d₂, X]

lemma simplex_pair_first_face_cone_vertex_formula {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨1, r, cone a, b⟩ : Pr N) = X 0 r a b - X 0 r v0 b := by
  rw [simplex_pair_first_face_succ_alternating_sum, Fin.sum_univ_two]
  have h1 : SimplexCategory.δ (1 : Fin 2) ≫ cone a = v0 := δ1_cone a
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, δ0_cone, h1, neg_smul, sub_eq_add_neg]

lemma simplex_pair_first_face_cone_succ_formula {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 2, r, cone a, b⟩ : Pr N) = X (p + 1) r a b - ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • X (p + 1) r (cone (SimplexCategory.δ i ≫ a)) b := by
  rw [simplex_pair_first_face_succ_alternating_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, δ0_cone, δsucc_cone, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

lemma simplex_pair_second_face_cone_succ_formula {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1 + 1, a, cone b⟩ : Pr N) = X p (r + 1) a b - ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • X p (r + 1) a (cone (SimplexCategory.δ i ≫ b)) := by
  rw [simplex_pair_second_face_succ_alternating_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, δ0_cone, δsucc_cone, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

lemma alt_const {N : ℕ} (p : ℕ) (Y : Pr N →₀ ℤ) :
    ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (if p = 0 then Y else 0) = 0 := by
  cases p with
  | zero => simp [Fin.sum_univ_two]
  | succ p => simp

lemma key {N : ℕ} (z : Pr N) (hz : z.1 + z.2.1 ≠ 0) :
    Pr.d N (H N (Finsupp.single z 1)) + H N (Pr.d N (Finsupp.single z 1)) = Finsupp.single z 1 := by
  obtain ⟨p, r, a, b⟩ := z
  change Pr.d N (H N (X p r a b)) + H N (Pr.d N (X p r a b)) = X p r a b
  cases p with
  | zero =>
    cases r with
    | zero => simp at hz
    | succ r =>
      rw [H_X, Hg_zero, map_add (f := _), d_X, d_X, d_X, simplex_pair_first_face_cone_vertex_formula, diffOne_zero, diffOne_zero, simplex_pair_second_face_cone_succ_formula, simplex_pair_second_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sub, map_sum, map_zsmul, H_X, Hg_zero, smul_add, Finset.sum_add_distrib, zero_add,
        pow_zero, pow_one, one_smul, neg_smul, map_zero]
      abel
  | succ p =>
    cases r with
    | zero =>
      rw [H_X, Hg_succ, d_X, d_X, simplex_pair_first_face_cone_succ_formula, simplex_pair_first_face_succ_alternating_sum, simplex_pair_second_face_of_vertex_eq_zero, simplex_pair_second_face_of_vertex_eq_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sub, map_sum, map_zsmul, H_X, smul_zero, add_zero, map_zero]
      simp only [Hg, smul_add, Finset.sum_add_distrib, alt_const, add_zero]
      abel
    | succ r =>
      rw [H_X, Hg_succ, d_X, d_X, simplex_pair_first_face_cone_succ_formula, simplex_pair_first_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sub, map_sum, map_zsmul, H_X, Hg_succ, map_zero]
      simp only [Hg, smul_add, Finset.sum_add_distrib, alt_const, add_zero]
      have e : (-1 : ℤ) ^ (p + 2) = -(-1) ^ (p + 1) := by ring
      rw [e, neg_smul]
      abel

lemma deg_H {N k : ℕ} {c : Pr N →₀ ℤ} (hdeg : Pr.Deg (k + 1) c) : Pr.Deg (k + 2) (H N c) := by
  intro z hz
  have e : H N c = ∑ y ∈ c.support, c y • Hg y := by
    simp [H, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [e] at hz
  obtain ⟨y, hy, hz2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have hz3 := Finsupp.support_smul hz2
  have hy' := hdeg y hy
  obtain ⟨p, r, a, b⟩ := y
  simp only [Hg] at hz3
  rcases Finset.mem_union.1 (Finsupp.support_add hz3) with h | h
  · have := Finsupp.support_single_subset h
    rw [Finset.mem_singleton] at this
    subst this
    change p + r = k + 1 at hy'
    change p + 1 + r = k + 2
    omega
  · split_ifs at h with hp
    · have := Finsupp.support_single_subset h
      rw [Finset.mem_singleton] at this
      subst this
      change p + r = k + 1 at hy'
      change 0 + (r + 1) = k + 2
      omega
    · simp at h

end LateralTheory.EtaleFoundations.AcycPf


open LateralTheory.EtaleFoundations.AcycPf in
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_acyc_of : LateralTheory.EtaleFoundations.SteenPf.leaf_acyc := by
  intro N k c hdeg hcyc
  refine ⟨LateralTheory.EtaleFoundations.AcycPf.H N c, LateralTheory.EtaleFoundations.AcycPf.deg_H hdeg, ?_⟩
  have h : ∀ y ∈ c.support, Pr.d N (LateralTheory.EtaleFoundations.AcycPf.H N (Finsupp.single y (c y))) + LateralTheory.EtaleFoundations.AcycPf.H N (Pr.d N (Finsupp.single y (c y))) =
      Finsupp.single y (c y) := by
    intro y hy
    have hy' := hdeg y hy
    rw [← Finsupp.smul_single_one, map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← smul_add, LateralTheory.EtaleFoundations.AcycPf.key y (by omega)]
  have e : Pr.d N (LateralTheory.EtaleFoundations.AcycPf.H N c) + LateralTheory.EtaleFoundations.AcycPf.H N (Pr.d N c) = c := by
    conv_rhs => rw [← Finsupp.sum_single c]
    conv_lhs => rw [← Finsupp.sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl h
  rw [hcyc, map_zero, add_zero] at e
  exact e

end
end

section -- merged from Development.EtaleCohomology.TateTwists.LeafWaPf
open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf.WaPf

def swap {N : ℕ} (z : Pr N) : Pr N := ⟨z.2.1, z.1, z.2.2.2, z.2.2.1⟩

noncomputable def tau (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun z => Finsupp.single (swap z) ((-1 : ℤ) ^ (z.1 * z.2.1))

lemma tau_single {N : ℕ} (z : Pr N) (n : ℤ) :
    tau N (Finsupp.single z n) = Finsupp.single (swap z) (n * (-1 : ℤ) ^ (z.1 * z.2.1)) := by
  simp [tau, Finsupp.linearCombination_single, Finsupp.smul_single]

lemma d_single {N : ℕ} (z : Pr N) (n : ℤ) :
    Pr.d N (Finsupp.single z n) = n • (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  simp [Pr.d, Finsupp.linearCombination_single]

lemma d_tau_single {N : ℕ} (z : Pr N) :
    Pr.d N (tau N (Finsupp.single z 1)) = tau N (Pr.d N (Finsupp.single z 1)) := by
  obtain ⟨p, r, a, b⟩ := z
  rw [tau_single, d_single, d_single]
  cases p with
  | zero =>
    cases r with
    | zero => simp [swap, Pr.d₁, Pr.d₂]
    | succ r =>
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [swap, Pr.d₁, Pr.d₂, map_add (f := _), map_smul, map_sum, tau_single, Finset.smul_sum,
        Finsupp.smul_single, smul_eq_mul]
      simp
  | succ p =>
    cases r with
    | zero =>
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [swap, Pr.d₁, Pr.d₂, map_add (f := _), map_smul, map_sum, tau_single, Finset.smul_sum,
        Finsupp.smul_single, smul_eq_mul]
      simp
    | succ r =>
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [swap, Pr.d₁, Pr.d₂, map_add (f := _), map_sum, tau_single, Finset.smul_sum,
        Finsupp.smul_single, smul_eq_mul, smul_add]
      rw [add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring_nf
        (try simp [pow_mul, mul_comm, mul_left_comm, mul_assoc])
        (try exact neg_one_pow_eq_or ℤ _)
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring_nf
        (try simp [pow_mul, mul_comm, mul_left_comm, mul_assoc])
        (try exact neg_one_pow_eq_or ℤ _)

lemma d_tau {N : ℕ} (c : Pr N →₀ ℤ) : Pr.d N (tau N c) = tau N (Pr.d N c) := by
  have : (Pr.d N).comp (tau N) = (tau N).comp (Pr.d N) := by
    refine Finsupp.lhom_ext' fun z => LinearMap.ext_ring ?_
    exact d_tau_single z
  exact LinearMap.congr_fun this c

lemma tau_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    tau M (Pr.push θ c) = Pr.push θ (tau N c) := by
  have : (tau M).comp (Pr.push θ) = (Pr.push θ).comp (tau N) := by
    refine Finsupp.lhom_ext fun z n => ?_
    simp only [LinearMap.comp_apply, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, tau_single]
    rfl
  exact LinearMap.congr_fun this c

lemma tau_bd {N : ℕ} (c : Pr N →₀ ℤ) : tau (N + 1) (Pr.bd c) = Pr.bd (tau N c) := by
  unfold Pr.bd
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, tau_push]

lemma wa_eq (N : ℕ) : Pr.wa N = tau N (Pr.aw N) := by
  unfold Pr.wa Pr.aw
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, tau_single, swap, one_mul]

end LateralTheory.EtaleFoundations.SteenPf.WaPf


open LateralTheory.EtaleFoundations.SteenPf LateralTheory.EtaleFoundations.SteenPf.WaPf in
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of_aw (hAW : leaf_aw) : leaf_wa := by
  intro N
  rw [wa_eq, wa_eq, d_tau, hAW, tau_bd]


open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of (hAW : leaf_aw) : leaf_wa := leaf_wa_of_aw hAW
end

namespace LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
theorem etale_steenrod_acyclic_models_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_acyc := by
  apply LateralTheory.EtaleFoundations.SteenPf.leaf_acyc_of
theorem etale_steenrod_alexander_whitney_compatibility_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_aw := by
  apply LateralTheory.EtaleFoundations.AwPf.leaf_aw_of
theorem etale_steenrod_whitney_alexander_compatibility_of_components : LateralTheory.EtaleFoundations.SteenPf.leaf_wa := by
  apply LateralTheory.EtaleFoundations.SteenPf.leaf_wa_of <;> first | exact etale_steenrod_alexander_whitney_compatibility_of_components
theorem etale_steenrod_power_operation_properties_of_components : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  apply LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney <;> first | exact etale_steenrod_acyclic_models_of_components | exact etale_steenrod_alexander_whitney_compatibility_of_components | exact etale_steenrod_whitney_alexander_compatibility_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := etale_steenrod_power_operation_properties_of_components
end LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy
end

namespace LateralTheory.Fix.CupProductTensor
open LateralTheory.EtaleFoundations

theorem cup_spec0 : t_cup_spec0 := LateralTheory.Fin.EtaleCupProductNaturalInCoefficients.etale_cup_product_compatibility_specification_of_components
theorem cup_assoc0 : EtaleCochainCupAssociativeOfPairing :=
  etale_cochain_cup_assoc_of_cup_spec_and_alexander_whitney_assoc cup_spec0 (t_aw_assoc0_of etale_chain_cochain_eval_basic_properties_hold simplicial_subinterval_of_subinterval_along_etale)
theorem secSep : EtaleTensorTripleProductLeibnizSeparated.SecSep := etale_sheaf_sections_separated_holds
theorem tens_tri : EtaleTensorPairProductAssociative :=
  etale_tensor_triple_product_of_family_and_leibniz (etale_tensor_triple_product_family_of_gluing LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange)
    (etale_tensor_triple_product_leibniz_of_separated secSep)
theorem tens_ex : tt_tens_ex := tt_tens_ex_of tt_tens_pre_of etale_presheaf_tensor_data_sheafification_is_tensor_complex
theorem univ_exdeg : twpair_tens_univ_exdeg := twpair_tens_univ_exdeg_of
theorem tens_univ : twpair_tens_univ := twpair_tens_univ_of univ_exdeg
theorem tens_ge : tt_tens_ge := tt_tens_ge_of (by intro R _ I J K τ hτ; exact (tens_univ R τ hτ).2.1)
theorem res_side : tt_res_side := tt_res_side_of tens_univ LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange
theorem twres_ext : EtaleTwistResolutionUniversalExtension := LateralTheory.Fin.EtaleTwistResolutionUniversalExtension.intersectionNumber_baseChange
theorem cup_compat : EtaleCupProductNaturalInCoefficients := LateralTheory.Fin.EtaleCupProductNaturalInCoefficients.intersectionNumber_baseChange

theorem holds_of (hts : EtaleTateTwistSectionsLocallyGenerated) :
    EtaleTwistedCupProductAssociative ∧ EtaleTwistResolutionPairingCupUnique := by
  have hsec : TwMulGenMap.twSec := hts
  have hloc : EtaleTateTwistSectionsLocallyMultiplesOfGenerator := fun q _ i => (hts q i).1
  have hinj : EtaleTateTwistGeneratorMapSectionsInjective := etale_tate_twist_generator_map_injective_of_sections_glue hts LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
    LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange
  have tw_mul : EtaleTateTwistSingletonTensorGenMul := etale_tate_twist_tensor_iso_of_generator_map_iso (etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists tens_ex) (etale_tate_twist_multiplication_generator_map_of_section_description hsec)
    (etale_tate_twist_generator_map_isIso_of_inj_surj etale_sheaf_mono_epi_iff_sections_of_separation (etale_tate_twist_generator_map_surjective_of_local_and_root hloc
      etale_tate_twist_generator_restriction_and_root_change_holds) hinj)
  have twist : tt_twist_side := tt_twist_side_of tw_mul LateralTheory.Fin.EtaleTateTwistSheafFlat.intersectionNumber_baseChange LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange
    LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange
  have twres : EtaleTensorPairTwistResolutionMul := etale_tensor_twisted_resolution_of_existence_bound_and_sides tens_ex tens_ge twist res_side
  have pa : t_pair_assoc := t_pair_assoc_of twres tens_tri twres_ext cup_compat cup_assoc0 t_pa_tens_ex_of
    t_pa_tens_univ_of t_pa_precomp_of t_pa_cpush_id_of t_pa_cpush_htpy_of
  have tp : EtaleTwistResolutionPairingCupUnique := etale_tate_twist_cup_pairing_of_tensor_and_resolution_properties tens_ex tens_univ twres twres_ext cup_compat twpair_zc_fun_of
  exact ⟨etale_twisted_cup_assoc_of_twisted_pairing_exists_assoc (t_twpair_ex_of tp) pa, tp⟩

theorem ringAssoc : LateralTheory.E.CupProductRingLaws.LeafRingAssoc := (holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).1
theorem cupSpec : LateralTheory.E.CupProductRingLaws.LeafCupSpec := fun R _ _ _ _ μ E _ _ _ hk => cup_spec0 R μ (E := E) hk
theorem ringComm (hf : cc_cup_flip) : LateralTheory.E.CupProductRingLaws.LeafRingComm :=
  etale_twisted_cup_graded_comm_of_flip_and_unique_pairing hf (fun R _ _ _ _ μ => (LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange R μ).imp fun _ h => h.1) (holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).2
theorem awFlip : cc_aw_flip := cc_aw_flip_of LateralTheory.Fin.PrismAlexanderWhitneySwapChainHomotopy.intersectionNumber_baseChange cupflip_eta_delta_of

theorem cupFlip : cc_cup_flip := by
  intro R _ I J K μ ν hf E n m k h h' a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (cupSpec R μ E h).1 α β
  obtain ⟨γ', hγ'⟩ := (cupSpec R ν E h').1 β α
  rw [(cupSpec R μ E h).2 _ _ _ hγ, (cupSpec R ν E h').2 _ _ _ hγ']
  exact awFlip R μ ν hf E h h' α β γ γ' hγ hγ'
theorem ringComm' : LateralTheory.E.CupProductRingLaws.LeafRingComm := ringComm cupFlip
theorem twPairExists : LateralTheory.E.CupProductRingLaws.LeafTwPairExists := fun q _ i j => ⟨_, ((holds_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec).2 q i j).1⟩
end LateralTheory.Fix.CupProductTensor
