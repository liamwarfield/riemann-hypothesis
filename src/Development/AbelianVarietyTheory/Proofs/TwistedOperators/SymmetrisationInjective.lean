module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMinusSignsHalfOfEven

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdPLinIsHomogeneous
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section
namespace GlobalTheory.InducedPBW.Onto

private lemma UgF_mono {p q j k : ℕ} (h : j ≤ k) : UgF p q j ≤ UgF p q k :=
  Submodule.span_mono fun _ ⟨l, hl, hu⟩ => ⟨l, hl.trans h, hu⟩

theorem indF_mono {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {j k : ℕ} (h : j ≤ k) : indF act j ≤ indF act k := by
  refine Submodule.span_mono ?_
  rintro z ⟨u, hu, v, rfl⟩
  exact ⟨u, UgF_mono h hu, v, rfl⟩

theorem indFlt_le {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (k : ℕ) : indFlt act k ≤ indF act k := by
  unfold indFlt
  exact iSup₂_le fun j hj => indF_mono act hj.le

theorem le_indFlt {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {j k : ℕ} (h : j < k) : indF act j ≤ indFlt act k := by
  unfold indFlt
  exact le_iSup₂ (f := fun i (_ : i < k) => indF act i) j h

theorem pLin_isHomogeneous {p q : ℕ} (Z : Mat p q) : (pLin Z).IsHomogeneous 1 := by
  unfold pLin
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun ab _ => MvPolynomial.isHomogeneous_C_mul_X _ _

theorem prod_pLin_isHomogeneous {p q : ℕ} (l : List (Mat p q)) :
    (l.map pLin).prod.IsHomogeneous l.length := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.length_nil]
    exact MvPolynomial.isHomogeneous_one _ _
  | cons Z l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm]
    exact (pLin_isHomogeneous Z).mul ih

theorem prod_mem_UgF {p q k : ℕ} (l : List (Mat p q)) (h : l.length ≤ k) :
    (l.map (ugι p q)).prod ∈ UgF p q k := Submodule.subset_span ⟨l, h, rfl⟩

theorem symProd_mem_UgF {p q k m : ℕ} (x : Fin m → Mat p q) (h : m ≤ k) :
    symProd (fun i => ugι p q (x i)) ∈ UgF p q k := by
  unfold symProd
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => ?_)
  have hmem := prod_mem_UgF (k := k) (List.ofFn fun i => x (σ i)) (by rw [List.length_ofFn]; exact h)
  rw [List.map_ofFn] at hmem
  exact hmem

theorem symU_mem_UgF {p q k : ℕ} (f : MvPolynomial (PIx p q) ℂ) (hf : f.IsHomogeneous k) :
    symU p q f ∈ UgF p q k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : d.degree = k := by
    by_contra hne
    exact MvPolynomial.mem_support_iff.mp hd (hf.coeff_eq_zero hne)
  have e : MvPolynomial.monomial d (f.coeff d) =
      f.coeff d • (MvPolynomial.basisMonomials (PIx p q) ℂ) d := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [symU, Module.Basis.constr_basis]
  refine symProd_mem_UgF _ (le_of_eq ?_)
  rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hdeg]
  rfl

private lemma mkQ_tmul_prod_mem_indFlt_sup {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hc : SymbolCongr act) (k : ℕ)
    (l : List (Mat p q)) (hl : l.length ≤ k) (v : V) :
    (indRel act).mkQ (TensorProduct.tmul ℂ (l.map (ugι p q)).prod v) ∈ indFlt act k ⊔
      (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
  rcases lt_or_eq_of_le hl with hlt | heq
  · refine Submodule.mem_sup_left (le_indFlt act hlt ?_)
    exact Submodule.subset_span ⟨_, prod_mem_UgF l le_rfl, v, rfl⟩
  · subst heq
    have hP : (l.map pLin).prod ∈ homog (PIx p q) l.length :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (prod_pLin_isHomogeneous l)
    have hs : (indRel act).mkQ (TensorProduct.tmul ℂ (symU p q (l.map pLin).prod) v) ∈
        (symTens p q V l.length).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
      refine ⟨LinearMap.rTensor V (homog (PIx p q) l.length).subtype
        (TensorProduct.tmul ℂ (⟨_, hP⟩ : homog (PIx p q) l.length) v), LinearMap.mem_range_self _ _, ?_⟩
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply]
    have hsum := Submodule.add_mem_sup (hc l v) hs
    rw [sub_add_cancel] at hsum
    exact hsum

theorem indF_eq_sup (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hc : SymbolCongr act) (k : ℕ) :
    indF act k = indFlt act k ⊔
      (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨u, hu, v, rfl⟩
    have key : UgF p q k ≤ (indFlt act k ⊔
        (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q))).comap
        ((indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v) := by
      refine Submodule.span_le.mpr ?_
      rintro w ⟨l, hl, rfl⟩
      exact mkQ_tmul_prod_mem_indFlt_sup act hc k l hl v
    exact key hu
  · refine sup_le (indFlt_le act k) ?_
    rintro _ ⟨z, ⟨w, rfl⟩, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f v =>
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply]
      exact Submodule.subset_span
        ⟨_, symU_mem_UgF f.1 ((MvPolynomial.mem_homogeneousSubmodule _ _).mp f.2), v, rfl⟩
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem ha hb

end GlobalTheory.InducedPBW.Onto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UgMemSpanListProd
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section

namespace GlobalTheory.InducedPBW

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem ug_mem_span_listProd (p q : ℕ) (u : Ug p q) :
    u ∈ Submodule.span ℂ {u : Ug p q | ∃ l : List (Mat p q), u = (l.map (ugι p q)).prod} := by
  have htop : Algebra.adjoin ℂ (Set.range (ugι p q)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (Mat p q)) :=
      RingCon.mkₐ_surjective _
    obtain ⟨t, rfl⟩ := hs x
    induction t using TensorAlgebra.induction with
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | ι y => exact Algebra.subset_adjoin ⟨y, rfl⟩
    | mul a b ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
    | add a b ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
  have hu : u ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (ugι p q))) := by
    rw [Subalgebra.mem_toSubmodule, htop]
    exact Algebra.mem_top
  rw [Algebra.adjoin_eq_span] at hu
  refine Submodule.span_mono (fun x hx => ?_) hu
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    exact ⟨[m], by simp⟩
  | one => exact ⟨[], by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨la, rfl⟩ := ha
    obtain ⟨lb, rfl⟩ := hb
    exact ⟨la ++ lb, by simp [List.map_append, List.prod_append]⟩

theorem iSup_indF_eq_top (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : (⨆ k, indF act k) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective (indRel act) z
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact add_mem ha hb
  | tmul u v =>
    have hu := ug_mem_span_listProd p q u
    induction hu using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨l, rfl⟩ := hw
      refine Submodule.mem_iSup_of_mem l.length (Submodule.subset_span ⟨_, ?_, v, rfl⟩)
      exact Submodule.subset_span ⟨l, le_rfl, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [TensorProduct.add_tmul, map_add (f := _)]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [← TensorProduct.smul_tmul', map_smul]
      exact Submodule.smul_mem _ c ha

end GlobalTheory.InducedPBW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeSingleAdd
open MvPolynomial TensorProduct

noncomputable section

namespace GlobalTheory.InducedPBW

section General

variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]

def zv (α : ι →₀ ℕ) : V →ₗ[R] (MvPolynomial ι R ⊗[R] V) :=
  TensorProduct.mk R (MvPolynomial ι R) V (monomial α 1)

def mulX (i : ι) : Module.End R (MvPolynomial ι R ⊗[R] V) :=
  LinearMap.rTensor V (LinearMap.mulLeft R (X i))

lemma mulX_zv (i : ι) (α : ι →₀ ℕ) (v : V) :
    mulX i (zv (R := R) α v) = zv (Finsupp.single i 1 + α) v := by
  simp [mulX, zv, X, monomial_mul]

def degLt (R : Type*) [CommRing R] (ι : Type*) (V : Type*) [AddCommGroup V] [Module R V] (n : ℕ) :
    Submodule R (MvPolynomial ι R ⊗[R] V) :=
  Submodule.span R {m | ∃ (α : ι →₀ ℕ) (v : V), α.degree < n ∧ m = zv α v}

lemma zv_mem {n : ℕ} {α : ι →₀ ℕ} (h : α.degree < n) (v : V) : zv α v ∈ degLt R ι V n :=
  Submodule.subset_span ⟨α, v, h, rfl⟩

lemma degLt_mono {n m : ℕ} (h : n ≤ m) : degLt R ι V n ≤ degLt R ι V m :=
  Submodule.span_mono fun _ ⟨α, v, h1, h2⟩ => ⟨α, v, h1.trans_le h, h2⟩

lemma map_degLt {W : Type*} [AddCommGroup W] [Module R W] {n : ℕ}
    (f : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W) (N : Submodule R W)
    (h : ∀ α v, α.degree < n → f (zv α v) ∈ N) : ∀ m ∈ degLt R ι V n, f m ∈ N := by
  have : degLt R ι V n ≤ N.comap f := Submodule.span_le.mpr (by
    rintro _ ⟨α, v, h1, rfl⟩
    exact h α v h1)
  exact fun m hm => this hm

lemma eq_on_degLt {W : Type*} [AddCommGroup W] [Module R W] {n : ℕ}
    (f f' : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W)
    (h : ∀ α v, α.degree < n → f (zv α v) = f' (zv α v)) : ∀ m ∈ degLt R ι V n, f m = f' m := by
  intro m hm
  have := map_degLt (f - f') ⊥ (fun α v hα => by simp [h α v hα]) m hm
  simpa [sub_eq_zero] using this

lemma ext_zv {W : Type*} [AddCommGroup W] [Module R W]
    {f f' : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W}
    (h : ∀ α v, f (zv α v) = f' (zv α v)) : f = f' := by
  apply TensorProduct.ext
  apply (basisMonomials ι R).ext
  intro α
  ext v
  simpa [zv] using h α v

lemma degree_single_add (i : ι) (α : ι →₀ ℕ) :
    (Finsupp.single i 1 + α).degree = α.degree + 1 := by
  simp [add_comm]

lemma mulX_mem {n : ℕ} (i : ι) : ∀ m ∈ degLt R ι V n, mulX i m ∈ degLt R ι V (n + 1) :=
  map_degLt _ _ fun α v h => by
    rw [mulX_zv]
    exact zv_mem (by rw [degree_single_add]; omega) v

variable {g : Type*} [LieRing g] [LieAlgebra R g]

lemma exists_extend (D : (ι →₀ ℕ) → g →ₗ[R] V →ₗ[R] (MvPolynomial ι R ⊗[R] V)) :
    ∃ δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V), ∀ x α v, δ x (zv α v) = D α x v := by
  refine ⟨{ toFun := fun x => TensorProduct.lift ((basisMonomials ι R).constr R fun α => D α x)
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  all_goals
    have key : ∀ (x : g) α v, TensorProduct.lift ((basisMonomials ι R).constr R fun α => D α x)
        (zv α v) = D α x v := by
      intro x α v
      have := (basisMonomials ι R).constr_basis R (fun α => D α x) α
      simp only [coe_basisMonomials] at this
      simp [zv, this]
  · intro x y
    exact ext_zv fun α v => by rw [LinearMap.add_apply, key, key, key]; simp
  · intro r x
    exact ext_zv fun α v => by rw [LinearMap.smul_apply, key, key]; simp
  · exact key

def extend (D : (ι →₀ ℕ) → g →ₗ[R] V →ₗ[R] (MvPolynomial ι R ⊗[R] V)) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := (exists_extend D).choose

lemma extend_zv (D : (ι →₀ ℕ) → g →ₗ[R] V →ₗ[R] (MvPolynomial ι R ⊗[R] V)) (x α v) :
    extend D x (zv α v) = D α x v := (exists_extend D).choose_spec x α v

variable [Fintype ι] [LinearOrder ι] (e : ι → g) (c : ι → g →ₗ[R] R) (act : g →ₗ[R] Module.End R V)

def mulLin : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := ∑ i, (c i).smulRight (mulX i)

omit [LinearOrder ι] in
lemma mulLin_apply (x : g) (m : MvPolynomial ι R ⊗[R] V) :
    mulLin c x m = ∑ i, c i x • mulX i m := by
  simp [mulLin, LinearMap.sum_apply]

omit [LinearOrder ι] in
lemma mulLin_mem {n : ℕ} (x : g) : ∀ m ∈ degLt R ι V n, mulLin c x m ∈ degLt R ι V (n + 1) := by
  intro m hm
  rw [mulLin_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mulX_mem i m hm)

def rho (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := mulLin c + δ

omit [LinearOrder ι] in
lemma rho_apply (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (x m) :
    rho c δ x m = mulLin c x m + δ x m := rfl

def strip (s : Finset ι) : g →ₗ[R] g := LinearMap.id - ∑ j ∈ s, (c j).smulRight (e j)

omit [Fintype ι] [LinearOrder ι] in
lemma strip_apply (s : Finset ι) (x : g) : strip e c s x = x - ∑ j ∈ s, c j x • e j := by
  simp [strip, LinearMap.sum_apply]

def straighten (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (i : ι) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) :=
  (LinearMap.mulLeft R (rho c δ (e i)) ∘ₗ δ -
    rho c δ ∘ₗ (LieAlgebra.ad R g (e i))) ∘ₗ strip e c (Finset.univ.filter (· ≤ i))

lemma straighten_apply (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (i : ι) (x m) :
    straighten e c δ i x m =
      rho c δ (e i) (δ (strip e c (Finset.univ.filter (· ≤ i)) x) m) +
      rho c δ ⁅strip e c (Finset.univ.filter (· ≤ i)) x, e i⁆ m := by
  rw [← lie_skew (strip e c (Finset.univ.filter (· ≤ i)) x), map_neg]
  simp [straighten, sub_eq_add_neg]

def step (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) :=
  extend fun α => if h : α.support.Nonempty then
    (straighten e c δ (α.support.min' h)).compl₂ (zv (α - Finsupp.single (α.support.min' h) 1))
  else (act ∘ₗ strip e c Finset.univ).compr₂ (zv 0)

lemma step_zero (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (x v) :
    step e c act δ x (zv 0 v) = zv 0 (act (strip e c Finset.univ x) v) := by
  simp [step, extend_zv]

lemma step_succ (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (i : ι) (J : ι →₀ ℕ)
    (hJ : ∀ j ∈ J.support, i ≤ j) (x v) :
    step e c act δ x (zv (Finsupp.single i 1 + J) v) = straighten e c δ i x (zv J v) := by
  have hi : i ∈ (Finsupp.single i 1 + J).support := by simp
  have hmin : (Finsupp.single i 1 + J).support.min' ⟨i, hi⟩ = i := by
    apply le_antisymm (Finset.min'_le _ _ hi)
    apply Finset.le_min'
    intro j hj
    rcases Finset.mem_union.mp (Finsupp.support_add hj) with h1 | h1
    · exact (Finset.mem_singleton.mp (Finsupp.support_single_subset h1)).ge
    · exact hJ j h1
  simp [step, extend_zv, hmin]

omit [Fintype ι] in
lemma exponent_cases (α : ι →₀ ℕ) :
    α = 0 ∨ ∃ (i : ι) (J : ι →₀ ℕ), (∀ j ∈ J.support, i ≤ j) ∧ α = Finsupp.single i 1 + J := by
  by_cases h : α.support.Nonempty
  · right
    refine ⟨α.support.min' h, α - Finsupp.single (α.support.min' h) 1, fun j hj => ?_, ?_⟩
    · exact Finset.min'_le _ _ (Finsupp.support_tsub hj)
    · rw [add_comm, tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (Finset.min'_mem _ h))
  · left
    simpa using h

def Pres (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) : Prop :=
  ∀ n x, ∀ m ∈ degLt R ι V n, δ x m ∈ degLt R ι V n

omit [LinearOrder ι] in
lemma Pres.rho_mem {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)} (h : Pres δ) (n x) :
    ∀ m ∈ degLt R ι V n, rho c δ x m ∈ degLt R ι V (n + 1) := fun m hm =>
  Submodule.add_mem _ (mulLin_mem c x m hm) (degLt_mono (Nat.le_succ n) (h n x m hm))

lemma Pres.step {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)} (h : Pres δ) :
    Pres (step e c act δ) := by
  intro n x
  refine map_degLt _ _ fun α v hα => ?_
  rcases exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩
  · rw [step_zero]; exact zv_mem hα _
  · rw [step_succ e c act δ i J hJ, straighten_apply]
    rw [degree_single_add] at hα
    have hz : zv J v ∈ degLt R ι V (J.degree + 1) := zv_mem (by omega) v
    refine degLt_mono (show J.degree + 1 + 1 ≤ n by omega) (Submodule.add_mem _ ?_ ?_)
    · exact h.rho_mem c _ _ _ (h _ _ _ hz)
    · exact h.rho_mem c _ _ _ hz

lemma step_agree {δ δ' : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)} (h : Pres δ) {n : ℕ}
    (ha : ∀ x, ∀ m ∈ degLt R ι V n, δ x m = δ' x m) :
    ∀ x, ∀ m ∈ degLt R ι V (n + 1), step e c act δ x m = step e c act δ' x m := by
  intro x
  refine eq_on_degLt _ _ fun α v hα => ?_
  rcases exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩
  · rw [step_zero, step_zero]
  · rw [step_succ e c act δ i J hJ, step_succ e c act δ' i J hJ, straighten_apply,
      straighten_apply]
    rw [degree_single_add] at hα
    have hz : zv J v ∈ degLt R ι V n := zv_mem (by omega) v
    simp only [rho_apply]
    rw [ha _ _ (h _ _ _ hz), ha _ _ hz, ha _ _ hz]

lemma exists_fixed : ∃ δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V),
    Pres δ ∧ step e c act δ = δ := by
  let d : ℕ → g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := fun n => (step e c act)^[n] 0
  have hd : ∀ n, d (n + 1) = step e c act (d n) := fun n => Function.iterate_succ_apply' _ _ _
  have hp : ∀ n, Pres (d n) := by
    intro n
    induction n with
    | zero => intro n x m _; simp [d]
    | succ n ih => rw [hd]; exact ih.step e c act
  have hag : ∀ n k, ∀ x, ∀ m ∈ degLt R ι V n, d n x m = d (n + k) x m := by
    intro n
    induction n with
    | zero =>
      intro k x
      exact eq_on_degLt _ _ fun α v h => absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro k
      rw [show n + 1 + k = (n + k) + 1 by omega, hd, hd]
      exact step_agree e c act (hp n) (ih k)
  let δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) :=
    extend fun α => (d (α.degree + 1)).compl₂ (zv α)
  have hδ : ∀ x α v, δ x (zv α v) = d (α.degree + 1) x (zv α v) := by
    intro x α v
    simp [δ, extend_zv]
  have hδn : ∀ n x, ∀ m ∈ degLt R ι V n, d n x m = δ x m := by
    intro n x
    refine eq_on_degLt _ _ fun α v h => ?_
    obtain ⟨k, rfl⟩ : ∃ k, n = α.degree + 1 + k := ⟨n - (α.degree + 1), by omega⟩
    rw [hδ, ← hag _ k x _ (zv_mem (Nat.lt_succ_self _) v)]
  refine ⟨δ, fun n x m hm => ?_, ?_⟩
  · rw [← hδn n x m hm]; exact hp n n x m hm
  · ext1 x
    refine ext_zv fun α v => ?_
    rw [hδ, hd]
    exact (step_agree e c act (hp _) (hδn _) x _ (zv_mem (Nat.lt_succ_self _) v)).symm

section Fixed

variable {e c act} {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)}
  (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)

include hce

omit [Fintype ι] in
lemma strip_e_mem {s : Finset ι} {i : ι} (hi : i ∈ s) : strip e c s (e i) = 0 := by
  simp [strip_apply, hce, hi]

omit [Fintype ι] in
lemma c_strip {s : Finset ι} {i : ι} (hi : i ∈ s) (x : g) : c i (strip e c s x) = 0 := by
  simp [strip_apply, hce, hi]

omit hce [Fintype ι] [LinearOrder ι] in
lemma strip_eq {s : Finset ι} {x : g} (hx : ∀ j ∈ s, c j x = 0) : strip e c s x = x := by
  rw [strip_apply, Finset.sum_eq_zero fun j hj => by rw [hx j hj, zero_smul], sub_zero]

lemma mulLin_e (i : ι) (m : MvPolynomial ι R ⊗[R] V) : mulLin c (e i) m = mulX i m := by
  simp [mulLin_apply, hce]

variable (hf : step e c act δ = δ)
include hf

lemma rho_e_le (i : ι) (α : ι →₀ ℕ) (h : ∀ j ∈ α.support, i ≤ j) (v : V) :
    rho c δ (e i) (zv α v) = zv (Finsupp.single i 1 + α) v := by
  rw [rho_apply, mulLin_e hce, mulX_zv, ← hf]
  rcases exponent_cases α with rfl | ⟨j, J, hJ, rfl⟩
  · rw [step_zero, strip_e_mem hce (Finset.mem_univ _)]
    simp
  · have hij : i ≤ j := h j (by simp)
    rw [step_succ e c act δ j J hJ, straighten_apply, strip_e_mem hce (by simpa using hij)]
    simp

omit hce hf [Fintype ι] in
lemma le_support_add {i j : ι} {J : ι →₀ ℕ} (hJ : ∀ k ∈ J.support, i ≤ k) (hij : i ≤ j) :
    ∀ k ∈ (Finsupp.single j 1 + J).support, i ≤ k := by
  intro k hk
  rcases Finset.mem_union.mp (Finsupp.support_add hk) with h1 | h1
  · exact hij.trans (Finset.mem_singleton.mp (Finsupp.support_single_subset h1)).ge
  · exact hJ k h1

lemma comm_high (i : ι) (J : ι →₀ ℕ) (hJ : ∀ j ∈ J.support, i ≤ j) (x : g)
    (hx : ∀ j, j ≤ i → c j x = 0) (v : V) :
    rho c δ x (rho c δ (e i) (zv J v)) =
      rho c δ (e i) (rho c δ x (zv J v)) + rho c δ ⁅x, e i⁆ (zv J v) := by
  rw [rho_e_le hce hf i J hJ, rho_apply c δ x, rho_apply c δ x, map_add (f := _)]
  conv_lhs => rw [← hf]
  rw [step_succ e c act δ i J hJ, straighten_apply,
    strip_eq (fun j hj => hx j (by simpa using hj)), ← add_assoc]
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mulLin_apply, mulLin_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ≤ i
  · simp [hx j hj]
  · rw [map_smul, mulX_zv, mulX_zv,
      rho_e_le hce hf i _ (le_support_add hJ (not_le.mp hj).le), add_left_comm]

def defect (c : ι → g →ₗ[R] R) (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V))
    (m : MvPolynomial ι R ⊗[R] V) : g →ₗ[R] g →ₗ[R] (MvPolynomial ι R ⊗[R] V) :=
  LinearMap.mk₂ R (fun x y => rho c δ x (rho c δ y m) - rho c δ y (rho c δ x m) - rho c δ ⁅x, y⁆ m)
    (by intros; simp only [add_lie, map_add (f := _), LinearMap.add_apply]; abel)
    (by intros; simp only [smul_lie, map_smul, LinearMap.smul_apply, smul_sub])
    (by intros; simp only [lie_add, map_add (f := _), LinearMap.add_apply]; abel)
    (by intros; simp only [lie_smul, map_smul, LinearMap.smul_apply, smul_sub])

omit hce hf [LinearOrder ι] in
lemma defect_apply (m : MvPolynomial ι R ⊗[R] V) (x y : g) : defect c δ m x y =
    rho c δ x (rho c δ y m) - rho c δ y (rho c δ x m) - rho c δ ⁅x, y⁆ m := rfl

omit hce hf [LinearOrder ι] in
lemma defect_swap (m : MvPolynomial ι R ⊗[R] V) (x y : g) :
    defect c δ m x y = - defect c δ m y x := by
  rw [defect_apply, defect_apply, ← lie_skew x y, map_neg, LinearMap.neg_apply]
  abel

lemma defect_e (i : ι) (J : ι →₀ ℕ) (hJ : ∀ j ∈ J.support, i ≤ j) (x : g) (v : V) :
    defect c δ (zv J v) x (e i) = 0 := by
  have hx : x = strip e c Finset.univ x + ∑ j, c j x • e j := by simp [strip_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_add (f := _), LinearMap.add_apply, map_sum, LinearMap.sum_apply, Finset.sum_eq_zero, add_zero]
  · rw [defect_apply, comm_high hce hf i J hJ _ fun j _ => c_strip hce (Finset.mem_univ _) x]
    abel
  · intro j _
    rw [map_smul, LinearMap.smul_apply]
    suffices h : defect c δ (zv J v) (e j) (e i) = 0 by rw [h, smul_zero]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [defect_apply, comm_high hce hf i J hJ _ fun k hk => by
        rw [hce, if_neg (hk.trans_lt h).ne]]
      abel
    · simp [defect_apply]
    · rw [defect_swap, defect_apply, comm_high hce hf j J (fun k hk => h.le.trans (hJ k hk)) _
        fun k hk => by rw [hce, if_neg (hk.trans_lt h).ne]]
      abel

omit hce hf [LinearOrder ι] in
lemma defect_strip (m : MvPolynomial ι R ⊗[R] V) (s : Finset ι)
    (h : ∀ j ∈ s, ∀ x, defect c δ m x (e j) = 0) (x y : g) :
    defect c δ m x y = defect c δ m (strip e c s x) (strip e c s y) := by
  have h' : ∀ j ∈ s, ∀ x, defect c δ m (e j) x = 0 := fun j hj x => by
    rw [defect_swap, h j hj, neg_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [strip_apply e c s y, map_sub, map_sum, Finset.sum_eq_zero fun j hj => by
    rw [map_smul, h j hj, smul_zero], sub_zero, strip_apply, map_sub, map_sum,
    LinearMap.sub_apply, LinearMap.sum_apply, Finset.sum_eq_zero fun j hj => by
    rw [map_smul, LinearMap.smul_apply, h' j hj, smul_zero], sub_zero]

omit hce in
lemma rho_zero_of_k (x : g) (hx : ∀ j, c j x = 0) (v : V) :
    rho c δ x (zv 0 v) = zv 0 (act x v) := by
  rw [rho_apply, ← hf, step_zero, strip_eq fun j _ => hx j, mulLin_apply]
  simp [hx]

lemma defect_eq_zero (hp : Pres δ)
    (hK : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) → ∀ j, c j ⁅x, y⁆ = 0)
    (hact : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) →
      act ⁅x, y⁆ = act x * act y - act y * act x) (n : ℕ) :
    ∀ x y, ∀ m ∈ degLt R ι V n, defect c δ m x y = 0 := by
  have lin : ∀ n x y, (∀ α v, α.degree < n → defect c δ (zv α v) x y = 0) →
      ∀ m ∈ degLt R ι V n, defect c δ m x y = 0 := by
    intro n x y h
    exact eq_on_degLt (rho c δ x * rho c δ y - rho c δ y * rho c δ x - rho c δ ⁅x, y⁆) 0 h
  induction n with
  | zero => exact fun x y => lin 0 x y fun α v h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    refine fun x y => lin _ x y fun α v hα => ?_
    rcases exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩
    · rw [defect_strip (e := e) _ Finset.univ fun j _ x => defect_e hce hf j 0 (by simp) x v]
      have hx := fun j => c_strip hce (Finset.mem_univ j) x
      have hy := fun j => c_strip hce (Finset.mem_univ j) y
      rw [defect_apply, rho_zero_of_k hf _ hx, rho_zero_of_k hf _ hy,
        rho_zero_of_k hf _ hx, rho_zero_of_k hf _ hy,
        rho_zero_of_k hf _ (hK _ _ hx hy), hact _ _ hx hy]
      simp
    · rw [defect_strip (e := e) _ (Finset.univ.filter (· ≤ i)) fun j hj x =>
        defect_e hce hf j _ (fun k hk => (show j ≤ i by simpa using hj).trans
          (le_support_add hJ le_rfl k hk)) x v]
      have hx : ∀ j, j ≤ i → c j (strip e c (Finset.univ.filter (· ≤ i)) x) = 0 :=
        fun j hj => c_strip hce (by simpa using hj) x
      have hy : ∀ j, j ≤ i → c j (strip e c (Finset.univ.filter (· ≤ i)) y) = 0 :=
        fun j hj => c_strip hce (by simpa using hj) y
      generalize strip e c (Finset.univ.filter (· ≤ i)) x = x at hx
      generalize strip e c (Finset.univ.filter (· ≤ i)) y = y at hy
      rw [degree_single_add] at hα
      have hz : zv J v ∈ degLt R ι V n := zv_mem (by omega) v
      have key : ∀ a b : g, (∀ j, j ≤ i → c j b = 0) →
          defect c δ (rho c δ b (zv J v)) a (e i) = 0 := by
        intro a b hb
        have : defect c δ (rho c δ b (zv J v)) a (e i) =
            ∑ j, c j b • defect c δ (mulX j (zv J v)) a (e i) +
              defect c δ (δ b (zv J v)) a (e i) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [defect_apply, rho_apply c δ b, mulLin_apply c b, map_add (f := _), map_sum, map_smul,
            smul_sub, Finset.sum_sub_distrib]
          abel
        rw [this, ih _ _ _ (hp _ _ _ hz), add_zero]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j ≤ i
        · simp [hb j hj]
        · rw [mulX_zv, defect_e hce hf i _ (le_support_add hJ (not_le.mp hj).le), smul_zero]
      have k1 := key x y hy
      have k2 := key y x hx
      have k3 := ih x y _ hz
      have k4 := ih ⁅x, e i⁆ y _ hz
      have k5 := ih x ⁅y, e i⁆ _ hz
      have k6 := ih ⁅x, y⁆ (e i) _ hz
      have k7 := congrArg (rho c δ x) (defect_e hce hf i J hJ y v)
      have k8 := congrArg (rho c δ y) (defect_e hce hf i J hJ x v)
      have k9 := congrArg (rho c δ (e i)) k3
      have jac : ⁅⁅x, y⁆, e i⁆ = ⁅⁅x, e i⁆, y⁆ + ⁅x, ⁅y, e i⁆⁆ := by
        rw [leibniz_lie x y (e i), ← lie_skew y ⁅x, e i⁆]; abel
      rw [← rho_e_le hce hf i J hJ]
      simp only [defect_apply, map_sub, map_zero, jac, map_add (f := _), LinearMap.add_apply] at *
      linear_combination (norm := abel1) k7 - k8 + k1 - k2 + k9 + k4 + k5 - k6

end Fixed

theorem exists_rep (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)
    (hK : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) → ∀ j, c j ⁅x, y⁆ = 0)
    (hact : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) →
      act ⁅x, y⁆ = act x * act y - act y * act x) :
    ∃ ρ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V),
      (∀ x y, ρ ⁅x, y⁆ = ρ x * ρ y - ρ y * ρ x) ∧
      (∀ x, (∀ j, c j x = 0) → ∀ v, ρ x (zv 0 v) = zv 0 (act x v)) ∧
      ∀ n x, ∀ m ∈ degLt R ι V n, ρ x m - mulLin c x m ∈ degLt R ι V n := by
  obtain ⟨δ, hp, hf⟩ := exists_fixed e c act
  refine ⟨rho c δ, fun x y => ext_zv fun α v => ?_, fun x hx v => rho_zero_of_k hf x hx v,
    fun n x m hm => by simpa [rho_apply] using hp n x m hm⟩
  have := defect_eq_zero hce hf hp hK hact _ x y _ (zv_mem (Nat.lt_succ_self α.degree) v)
  rw [defect_apply, sub_eq_zero] at this
  exact this.symm

end General

end GlobalTheory.InducedPBW
end
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible MvPolynomial TensorProduct

noncomputable section

namespace GlobalTheory.InducedPBW.Injective

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def coordP (ab : PIx p q) : Mat p q →ₗ[ℂ] ℂ := Matrix.entryLinearMap ℂ ℂ ab.1.1 ab.1.2

lemma isKC_iff (x : Mat p q) : (∀ j, coordP j x = 0) ↔ IsKC x := by
  constructor
  · intro h a b hab
    exact h ⟨(a, b), hab⟩
  · intro h j
    exact h j.1.1 j.1.2 j.2

private lemma sameBlock_trans_twisted_operators {a b c : Ix p q} (h1 : sameBlock a b) (h2 : sameBlock b c) :
    sameBlock a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock]

lemma isKC_mul {x y : Mat p q} (hx : IsKC x) (hy : IsKC y) : IsKC (x * y) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : sameBlock a c
  · have hcb : ¬ sameBlock c b := fun hcb => hab (sameBlock_trans_twisted_operators hac hcb)
    rw [hy c b hcb, mul_zero]
  · rw [hx a c hac, zero_mul]

lemma mulLin_tmul (x : Mat p q) (s : MvPolynomial (PIx p q) ℂ) (v : V) :
    mulLin coordP x (s ⊗ₜ[ℂ] v) = (pLin x * s) ⊗ₜ[ℂ] v := by
  rw [mulLin_apply]
  simp only [mulX, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, coordP,
    Matrix.entryLinearMap_apply]
  rw [pLin, Finset.sum_mul, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.smul_tmul', MvPolynomial.smul_eq_C_mul, mul_assoc]

lemma pLin_Eab (ab : PIx p q) : pLin (Eab ab.1.1 ab.1.2) = X ab := by
  unfold pLin
  rw [Finset.sum_eq_single ab]
  · simp [Eab]
  · intro b _ hb
    have : ¬ (ab.1.1 = b.1.1 ∧ ab.1.2 = b.1.2) := fun h =>
      hb (Subtype.ext (Prod.ext h.1.symm h.2.symm))
    simp [Eab, Matrix.single_apply_of_ne (h := this)]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma prod_map_X_eq_monomial' (L : List (PIx p q)) :
    (L.map (X : PIx p q → MvPolynomial (PIx p q) ℂ)).prod =
      monomial (Multiset.toFinsupp (L : Multiset (PIx p q))) 1 := by
  induction L with
  | nil => simp [Multiset.toFinsupp_zero, MvPolynomial.monomial_zero']
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, ← Multiset.cons_coe, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, MvPolynomial.X,
      MvPolynomial.monomial_mul, one_mul]

lemma exists_list (α : PIx p q →₀ ℕ) : ∃ l : List (Mat p q), l.length = α.degree ∧
    (l.map pLin).prod = monomial α 1 := by
  refine ⟨(Finsupp.toMultiset α).toList.map fun ab => Eab ab.1.1 ab.1.2, ?_, ?_⟩
  · rw [List.length_map, Multiset.length_toList, Finsupp.card_toMultiset, Finsupp.degree_apply]
    rfl
  · rw [List.map_map]
    have hc : (pLin ∘ fun ab : PIx p q => Eab ab.1.1 ab.1.2) = X := funext pLin_Eab
    rw [hc, prod_map_X_eq_monomial', Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]

private lemma coordP_Eab (i j : PIx p q) :
    coordP i (Eab j.1.1 j.1.2) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [coordP, Eab]
  · have hne : ¬ (j.1.1 = i.1.1 ∧ j.1.2 = i.1.2) := fun h' =>
      h (Subtype.ext (Prod.ext h'.1.symm h'.2.symm))
    simp [coordP, Eab, h, Matrix.single_apply_of_ne (h := hne)]

private lemma isKC_sub' {x y : Mat p q} (hx : IsKC x) (hy : IsKC y) : IsKC (x - y) := by
  intro a b hab
  rw [Matrix.sub_apply, hx a b hab, hy a b hab, sub_zero]

lemma exists_rep_gl (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (h : IsKLieAct act) :
    ∃ ρ : Ug p q →ₐ[ℂ] Module.End ℂ (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V),
      (∀ x, IsKC x → ∀ v, ρ (ugι p q x) (zv 0 v) = zv 0 (act x v)) ∧
      ∀ n x, ∀ m ∈ degLt ℂ (PIx p q) V n,
        ρ (ugι p q x) m - mulLin coordP x m ∈ degLt ℂ (PIx p q) V n := by
  let _ : LinearOrder (PIx p q) :=
    LinearOrder.lift' (Fintype.equivFin (PIx p q)) (Fintype.equivFin (PIx p q)).injective
  have hK : ∀ x y : Mat p q, (∀ j, coordP j x = 0) → (∀ j, coordP j y = 0) →
      ∀ j, coordP j ⁅x, y⁆ = 0 := by
    intro x y hx hy
    rw [Ring.lie_def]
    exact (isKC_iff _).mpr (isKC_sub' (isKC_mul ((isKC_iff x).mp hx) ((isKC_iff y).mp hy))
      (isKC_mul ((isKC_iff y).mp hy) ((isKC_iff x).mp hx)))
  have hact : ∀ x y : Mat p q, (∀ j, coordP j x = 0) → (∀ j, coordP j y = 0) →
      act ⁅x, y⁆ = act x * act y - act y * act x := by
    intro x y hx hy
    rw [Ring.lie_def]
    exact h x y ((isKC_iff x).mp hx) ((isKC_iff y).mp hy)
  obtain ⟨ρ, hbr, hk, hdeg⟩ := exists_rep (R := ℂ) (ι := PIx p q) (g := Mat p q) (V := V)
    (fun ab => Eab ab.1.1 ab.1.2) coordP act
    (fun i j => by rw [coordP_Eab]; split_ifs <;> rfl) hK hact
  let f : Mat p q →ₗ⁅ℂ⁆ Module.End ℂ (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V) :=
    { ρ with
      map_lie' := fun {x y} => by
        show ρ ⁅x, y⁆ = ⁅ρ x, ρ y⁆
        rw [hbr, Ring.lie_def] }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ f, fun x hx v => ?_, fun n x m hm => ?_⟩
  · rw [show ugι p q x = UniversalEnvelopingAlgebra.ι ℂ x from rfl,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hk x ((isKC_iff x).mpr hx) v
  · rw [show ugι p q x = UniversalEnvelopingAlgebra.ι ℂ x from rfl,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hdeg n x m hm

lemma prod_tmul_mem (l : List (Mat p q)) (v : V) :
    (l.map pLin).prod ⊗ₜ[ℂ] v ∈ degLt ℂ (PIx p q) V (l.length + 1) := by
  induction l with
  | nil =>
    have h1 : (1 : MvPolynomial (PIx p q) ℂ) ⊗ₜ[ℂ] v = zv 0 v := by
      simp [zv, MvPolynomial.monomial_zero']
    rw [List.map_nil, List.prod_nil, h1]
    exact zv_mem (by simp) v
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, ← mulLin_tmul, List.length_cons]
    exact mulLin_mem coordP x _ ih

lemma exists_symbol (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (h : IsKLieAct act) :
    ∃ φ : Ind act →ₗ[ℂ] (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V), ∀ (l : List (Mat p q)) (v : V),
      φ ((indRel act).mkQ ((l.map (ugι p q)).prod ⊗ₜ[ℂ] v)) - (l.map pLin).prod ⊗ₜ[ℂ] v ∈
        degLt ℂ (PIx p q) V l.length := by
  obtain ⟨ρ, hk, hdeg⟩ := exists_rep_gl act h
  let F : Ug p q →ₗ[ℂ] V →ₗ[ℂ] (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V) :=
    LinearMap.mk₂ ℂ (fun u v => ρ u (zv 0 v)) (fun u u' v => by simp) (fun c u v => by simp)
      (fun u v v' => by simp) (fun c u v => by simp)
  have hΦ : ∀ u v, TensorProduct.lift F (u ⊗ₜ[ℂ] v) = ρ u (zv 0 v) := fun u v => by
    simp [F]
  have hle : indRel act ≤ LinearMap.ker (TensorProduct.lift F) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨u, Y, v, hY, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hΦ, map_mul, Module.End.mul_apply,
      hk Y hY v, sub_self]
  refine ⟨(indRel act).liftQ (TensorProduct.lift F) hle, fun l v => ?_⟩
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, hΦ]
  induction l with
  | nil =>
    simp [zv, MvPolynomial.monomial_zero']
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, List.map_cons,
      List.prod_cons, List.length_cons]
    have hA : ρ (l.map (ugι p q)).prod (zv 0 v) ∈ degLt ℂ (PIx p q) V (l.length + 1) := by
      have h2 := Submodule.add_mem _ (degLt_mono (Nat.le_succ _) ih) (prod_tmul_mem l v)
      rwa [sub_add_cancel] at h2
    have e : ρ (ugι p q x) (ρ (l.map (ugι p q)).prod (zv 0 v)) - (pLin x * (l.map pLin).prod) ⊗ₜ[ℂ] v =
        (ρ (ugι p q x) (ρ (l.map (ugι p q)).prod (zv 0 v)) -
          mulLin coordP x (ρ (l.map (ugι p q)).prod (zv 0 v))) +
        mulLin coordP x (ρ (l.map (ugι p q)).prod (zv 0 v) - (l.map pLin).prod ⊗ₜ[ℂ] v) := by
      rw [map_sub, mulLin_tmul]
      abel
    rw [e]
    exact Submodule.add_mem _ (hdeg _ x _ hA) (mulLin_mem coordP x _ ih)

lemma eq_zero_of_mem {k : ℕ} {z : MvPolynomial (PIx p q) ℂ ⊗[ℂ] V} (h1 : z ∈ symTens p q V k)
    (h2 : z ∈ degLt ℂ (PIx p q) V k) : z = 0 := by
  have hfix : LinearMap.rTensor V (homogeneousComponent k) z = z := by
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp h1
    have hc : (homogeneousComponent k).comp (homog (PIx p q) k).subtype =
        (homog (PIx p q) k).subtype := by
      refine LinearMap.ext fun P => ?_
      simp [homogeneousComponent_of_mem P.2]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hc]
  have hkill : degLt ℂ (PIx p q) V k ≤
      LinearMap.ker (LinearMap.rTensor V (homogeneousComponent (σ := PIx p q) (R := ℂ) k)) := by
    refine Submodule.span_le.mpr ?_
    rintro m ⟨α, v, hα, rfl⟩
    have hm : (monomial α (1 : ℂ)) ∈ homogeneousSubmodule (PIx p q) ℂ α.degree :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial 1 rfl)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, zv, TensorProduct.mk_apply,
      LinearMap.rTensor_tmul, homogeneousComponent_of_mem hm, if_neg (Nat.ne_of_gt hα),
      TensorProduct.zero_tmul]
  have h3 := hkill h2
  rw [LinearMap.mem_ker, hfix] at h3
  exact h3

theorem symmetrisation_injective (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (h : IsKLieAct act)
    (hs : SymbolCongr act) (k : ℕ) (z) (hz : z ∈ symTens p q V k)
    (hz' : (indRel act).mkQ (LinearMap.rTensor V (symU p q) z) ∈ indFlt act k) : z = 0 := by
  obtain ⟨φ, hφ⟩ := exists_symbol act h
  have hF : ∀ j < k, indF act j ≤ (degLt ℂ (PIx p q) V k).comap φ := by
    intro j hj
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, v, rfl⟩
    let Lv : Ug p q →ₗ[ℂ] (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V) :=
      φ ∘ₗ (indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v
    have hU : UgF p q j ≤ (degLt ℂ (PIx p q) V k).comap Lv := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, hl, rfl⟩
      have h4 := Submodule.add_mem _ (degLt_mono (show l.length ≤ k by omega) (hφ l v))
        (degLt_mono (show l.length + 1 ≤ k by omega) (prod_tmul_mem l v))
      rw [sub_add_cancel] at h4
      exact h4
    exact hU hu
  have hlow : indFlt act k ≤ (degLt ℂ (PIx p q) V k).comap φ := by
    unfold indFlt
    exact iSup_le fun j => iSup_le fun hj => hF j hj
  have hsym : ∀ P : MvPolynomial (PIx p q) ℂ, P.IsHomogeneous k → ∀ v : V,
      φ ((indRel act).mkQ (symU p q P ⊗ₜ[ℂ] v)) - P ⊗ₜ[ℂ] v ∈ degLt ℂ (PIx p q) V k := by
    intro P hP v
    let M : MvPolynomial (PIx p q) ℂ →ₗ[ℂ] (MvPolynomial (PIx p q) ℂ ⊗[ℂ] V) :=
      φ ∘ₗ (indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v ∘ₗ symU p q -
        (TensorProduct.mk ℂ (MvPolynomial (PIx p q) ℂ) V).flip v
    have hM : ∀ Q, M Q = φ ((indRel act).mkQ (symU p q Q ⊗ₜ[ℂ] v)) - Q ⊗ₜ[ℂ] v := fun Q => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hM, P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hdeg : α.degree = k := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (mem_support_iff.mp hα)
    have hmon : monomial α (AddMonoidAlgebra.coeff P α) = AddMonoidAlgebra.coeff P α • monomial α (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [hM]
    obtain ⟨l, hl, hprod⟩ := exists_list α
    have hc := hs l v
    have h1 := hφ l v
    rw [hprod, hl, hdeg] at hc h1
    have h8 : φ ((indRel act).mkQ ((l.map (ugι p q)).prod ⊗ₜ[ℂ] v) -
        (indRel act).mkQ (symU p q (monomial α 1) ⊗ₜ[ℂ] v)) ∈ degLt ℂ (PIx p q) V k := hlow hc
    have key := Submodule.sub_mem _ h1 h8
    rw [map_sub, sub_sub_sub_cancel_left] at key
    exact key
  have hzsym : φ ((indRel act).mkQ (LinearMap.rTensor V (symU p q) z)) - z ∈
      degLt ℂ (PIx p q) V k := by
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hz
    clear hz hz'
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul P v =>
      simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype]
      exact hsym P.1 P.2 v
    | add w w' hw hw' =>
      have h5 := Submodule.add_mem _ hw hw'
      simp only [map_add (f := _)]
      rw [add_sub_add_comm]
      exact h5
  have hz0 : z ∈ degLt ℂ (PIx p q) V k := by
    have h7 : φ ((indRel act).mkQ (LinearMap.rTensor V (symU p q) z)) ∈ degLt ℂ (PIx p q) V k :=
      hlow hz'
    have h6 := Submodule.sub_mem _ h7 hzsym
    rwa [sub_sub_cancel] at h6
  exact eq_zero_of_mem hz hz0

end GlobalTheory.InducedPBW.Injective

namespace GlobalTheory.InducedPBW

theorem pbw_induced : admQ8 := by
  unfold admQ8
  intro p q V _ _ act h
  have hs := symbolCongr p q V act
  refine ⟨iSup_indF_eq_top p q V act, fun k => ⟨Onto.indF_eq_sup p q V act hs k,
    fun z hz hz' => Injective.symmetrisation_injective act h hs k z hz hz',
    fun Y hY z hz => symmetrisation_equivariant p q V act hs k Y hY z hz⟩⟩

end GlobalTheory.InducedPBW
