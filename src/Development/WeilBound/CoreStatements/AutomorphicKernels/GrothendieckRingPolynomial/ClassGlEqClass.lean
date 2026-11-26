module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PhiZAux

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZBijective
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleApply
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.SingleEqSmulSingle
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth

def Steps (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k

def R (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Type 1 := GrothGL k

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckRing

section Bil

variable {ι M : Type*} [AddCommGroup M]

def bil (C : ι → ι → M) (a b : ι →₀ ℤ) : M := a.sum fun x m => b.sum fun y n => (m * n) • C x y

variable (C : ι → ι → M)

theorem bil_add_right (a b c : ι →₀ ℤ) : bil C a (b + c) = bil C a b + bil C a c := by
  unfold bil
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun x _ => ?_
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [mul_add, add_smul])

theorem bil_add_left (a b c : ι →₀ ℤ) : bil C (a + b) c = bil C a c + bil C b c := by
  unfold bil
  refine Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => ?_)
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [add_mul, add_smul]

theorem bil_zero_left (b : ι →₀ ℤ) : bil C 0 b = 0 := by
  simp [bil]

theorem bil_zero_right (a : ι →₀ ℤ) : bil C a 0 = 0 := by
  simp [bil]

theorem bil_smul_left (z : ℤ) (a b : ι →₀ ℤ) : bil C (z • a) b = z • bil C a b := by
  unfold bil
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.smul_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [smul_eq_mul, mul_assoc, mul_smul]

theorem bil_smul_right (z : ℤ) (a b : ι →₀ ℤ) : bil C a (z • b) = z • bil C a b := by
  unfold bil
  rw [Finsupp.smul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [smul_eq_mul, mul_left_comm, mul_smul]

theorem bil_comm (hC : ∀ x y, C x y = C y x) (a b : ι →₀ ℤ) : bil C a b = bil C b a := by
  unfold bil
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun y _ => Finsupp.sum_congr fun x _ => ?_
  rw [mul_comm, hC]

theorem single_eq_smul_single (x : ι) (m : ℤ) : (Finsupp.single x m : ι →₀ ℤ) = m • Finsupp.single x 1 := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

end Bil

section BilAssoc

variable {ι : Type*} (C : ι → ι → ι →₀ ℤ)

theorem bil_assoc (hA : ∀ x y z, bil C (bil C (Finsupp.single x 1) (Finsupp.single y 1)) (Finsupp.single z 1) =
      bil C (Finsupp.single x 1) (bil C (Finsupp.single y 1) (Finsupp.single z 1))) (a b c : ι →₀ ℤ) :
    bil C (bil C a b) c = bil C a (bil C b c) := by
  induction a using Finsupp.induction_linear with
  | zero => simp only [bil_zero_left]
  | add a a' ha ha' => rw [bil_add_left, bil_add_left, bil_add_left, ha, ha']
  | single x m =>
    simp only [single_eq_smul_single x m, bil_smul_left]
    congr 1
    induction b using Finsupp.induction_linear with
    | zero => simp only [bil_zero_left, bil_zero_right]
    | add b b' hb hb' => rw [bil_add_right, bil_add_left, hb, hb', bil_add_left, bil_add_right]
    | single y n =>
      simp only [single_eq_smul_single y n, bil_smul_left, bil_smul_right]
      congr 1
      induction c using Finsupp.induction_linear with
      | zero => simp only [bil_zero_right]
      | add c c' hc hc' => rw [bil_add_right, bil_add_right, hc, hc', bil_add_right]
      | single z p =>
        simp only [single_eq_smul_single z p, bil_smul_right]
        congr 1
        exact hA x y z

theorem bil_one (u : ι →₀ ℤ) (h : ∀ x, bil C u (Finsupp.single x 1) = Finsupp.single x 1) (a : ι →₀ ℤ) :
    bil C u a = a := by
  induction a using Finsupp.induction_linear with
  | zero => rw [bil_zero_right]
  | add a a' ha ha' => rw [bil_add_right, ha, ha']
  | single x m => rw [single_eq_smul_single, bil_smul_right, h]

end BilAssoc

def cm (x y : IrrGL (k := k)) : GrothGL k := cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))

theorem mulR_eq (a b : GrothGL k) : mulR a b = bil cm a b := rfl

theorem sg_eq (x : IrrGL (k := k)) : sg x = Finsupp.single x 1 := rfl

theorem mulR_add (a b c : GrothGL k) : mulR a (b + c) = mulR a b + mulR a c := bil_add_right _ a b c

theorem add_mulR (a b c : GrothGL k) : mulR (a + b) c = mulR a c + mulR b c := bil_add_left _ a b c

theorem zero_mulR (a : GrothGL k) : mulR 0 a = 0 := bil_zero_left _ a

theorem mulR_zero (a : GrothGL k) : mulR a 0 = 0 := bil_zero_right _ a

theorem mulR_comm' [Fact (Comm k)] (a b : GrothGL k) : mulR a b = mulR b a := by
  rw [mulR_eq, mulR_eq]
  exact bil_comm _ (fun x y => (Fact.out : Comm k) x y) a b

theorem mulR_assoc' [Fact (Assoc k)] (a b c : GrothGL k) : mulR (mulR a b) c = mulR a (mulR b c) := by
  simp only [mulR_eq]
  refine bil_assoc _ (fun x y z => ?_) a b c
  have h := (Fact.out : Assoc k) x y z
  simp only [mulR_eq, sg_eq] at h
  exact h

theorem unit_mulR [Fact (One k)] (a : GrothGL k) : mulR (GrothGL.unit k) a = a := by
  rw [mulR_eq]
  refine bil_one _ _ (fun x => ?_) a
  have h := (Fact.out : One k) x
  simp only [mulR_eq, sg_eq] at h
  exact h

end GrothendieckRing

open GrothendieckRing

variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

instance instCommRingR : CommRing (R k) :=
  { (inferInstanceAs (AddCommGroup (GrothGL k)) : AddCommGroup (R k)) with
    mul := fun a b => mulR a b
    one := GrothGL.unit k
    left_distrib := fun a b c => mulR_add a b c
    right_distrib := fun a b c => add_mulR a b c
    zero_mul := fun a => zero_mulR a
    mul_zero := fun a => mulR_zero a
    mul_assoc := fun a b c => mulR_assoc' a b c
    one_mul := fun a => unit_mulR a
    mul_one := fun a => (mulR_comm' _ _).trans (unit_mulR a)
    mul_comm := fun a b => mulR_comm' a b }

def toR : GrothGL k ≃+ R k := { Equiv.refl _ with map_add' := fun _ _ => rfl }

theorem toR_mulR (a b : GrothGL k) : toR (mulR a b) = toR a * toR b := rfl

theorem toR_unit : toR (GrothGL.unit k) = 1 := rfl

def phiOf (f : Segment k → IrrGL (k := k)) : MvPolynomial (Segment k) ℤ →+* R k :=
  MvPolynomial.eval₂Hom (Int.castRingHom (R k)) fun Δ => toR (sg (f Δ))

theorem phiOf_X (f : Segment k → IrrGL (k := k)) (Δ : Segment k) : phiOf f (MvPolynomial.X Δ) = toR (sg (f Δ)) :=
  MvPolynomial.eval₂Hom_X' _ _ _

end PositivityTheory.Groth

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace PhiLAux

theorem exists_lseg (hs : LSegExists k) : ∃ Lseg : Segment k → IrrGL (k := k), ∀ Δ, IsLSeg Δ (Lseg Δ).rep := by
  choose π hπ using hs
  exact ⟨fun Δ => ⟨Δ.deg, (π Δ).cl⟩, fun Δ => (hπ Δ).of_equiv (equivRep (π Δ))⟩

theorem lfactors_sum {𝔪 : Multiset (Segment k)} {h : ℕ} {x : Fin h → IrrGL (k := k)} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨hΔ, -⟩, hxΔ⟩ := hx
  rw [← hΔ, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => ((hxΔ a).deg_eq).symm

theorem isL_deg {𝔪 : Multiset (Segment k)} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) : N = (𝔪.map Segment.deg).sum := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  rw [← hd, lfactors_sum hx]

theorem isL_cls_unique (hf : LOrderFree k) {𝔪 : Multiset (Segment k)} {x y : IrrGL (k := k)} (hx : IsL 𝔪 x.rep)
    (hy : IsL 𝔪 y.rep) : x = y := by
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  have e : n = m := (isL_deg hx).trans (isL_deg hy).symm
  subst e
  exact congrArg (Sigma.mk n) (irrCl_eq_iff.2 (GlobalTheory.T.langlands_classification_order_free_equiv hf 𝔪 _ _ hx hy))

theorem exists_orderedForm (𝔪 : Multiset (Segment k)) : ∃ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 := by
  obtain ⟨h₁, -, -, Δ₁, -, -, hΔ₁, -⟩ := GlobalTheory.T.ordered_forms_interleave_sum PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top 𝔪 0
  exact ⟨h₁, Δ₁, hΔ₁⟩

theorem class_apply_same_degree {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hl : HasFiniteLength π) (c : IrrCl (GL (Fin N) k)) : cl0 π ⟨N, c⟩ = ((jhMult c.rep.ρ π).toNat : ℤ) := by
  unfold cl0
  rw [dite_eq_left hl]
  exact (clsGL_apply π hl c).trans (cls_apply π hl c)


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem class_apply_other_degree {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (y : IrrGL (k := k)) (hy : y.1 ≠ N) : cl0 π y = 0 := by
  unfold cl0
  split_ifs with hl
  · rw [clsGL]
    exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨c, rfl⟩; exact hy rfl)
  · rfl

theorem class_product_irreducible_apply {h : ℕ} (x : Fin h → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1) :
    cl0 (prodIrr x (N := ∑ a, (x a).1) rfl) y = ((jhMult y.rep (prodIrr x hd)).toNat : ℤ) := by
  obtain ⟨n, c⟩ := y
  dsimp only at hd
  subst hd
  exact class_apply_same_degree _ (GlobalTheory.T.product_irreducible_finite_length PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top x _) c

theorem sum_sq_le (s : Multiset ℕ) : (s.map fun l => l ^ 2).sum ≤ s.sum ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    have h1 : (a + s.sum) ^ 2 = a ^ 2 + 2 * a * s.sum + s.sum ^ 2 := by ring
    have h2 := Nat.zero_le (2 * a * s.sum)
    rw [h1]
    linarith

theorem sq_le (𝔪 : Multiset (Segment k)) : PositivityTheory.Groth.sq 𝔪 ≤ (Multiset.card (msupp 𝔪)) ^ 2 := by
  have hc : Multiset.card (msupp 𝔪) = (𝔪.map Segment.len).sum := by
    rw [msupp, Multiset.card_bind]
    simp [Segment.card_ms]
  have hs : PositivityTheory.Groth.sq 𝔪 = ((𝔪.map Segment.len).map fun l => l ^ 2).sum := by
    rw [Multiset.map_map]
    rfl
  rw [hc, hs]
  exact sum_sq_le _

theorem prod_map_toMultiset {M : Type*} [CommMonoid M] {α : Type*} (g : α → M) (s : α →₀ ℕ) :
    ((Finsupp.toMultiset s).map g).prod = s.prod fun a n => g a ^ n := by
  refine Finsupp.induction s ?_ ?_
  · simp
  · intro a n f _ _ ih
    rw [map_add (f := _), Multiset.map_add (f := _), Multiset.prod_add, ih,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
      Multiset.prod_singleton]
    congr 1
    exact (Finsupp.prod_single_index (h := fun x m => g x ^ m) (pow_zero (g a))).symm

variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem toR_foldr (l : List (IrrGL (k := k))) :
    toR (l.foldr (fun y a => mulR (sg y) a) (GrothGL.unit k)) = (l.map fun y => toR (sg y)).prod := by
  induction l with
  | nil => simp [toR_unit]
  | cons y l ih => rw [List.foldr_cons, toR_mulR, ih, List.map_cons, List.prod_cons]

theorem ring_class_product_irreducible (hPL : ProdList k) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) :
    toR (cl0 (prodIrr x hd)) = ∏ a, toR (sg (x a)) := by
  rw [hPL h N x hd, toR_foldr, List.map_ofFn, List.prod_ofFn]
  rfl

end PhiLAux

variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem phiL_main (hk : Steps k) (h2 : UniTri) :
    ∃ Lseg : Segment k → IrrGL (k := k), (∀ Δ, IsLSeg Δ (Lseg Δ).rep) ∧ Function.Bijective (phiOf Lseg) ∧
      (∀ (𝔫 : Multiset (Segment k)) (x : IrrGL (k := k)), IsL 𝔫 x.rep →
        ∃ p : MvPolynomial (Segment k) ℤ, phiOf Lseg p = toR (sg x) ∧
          ∀ s ∈ p.support, msupp (Finsupp.toMultiset s) = msupp 𝔫) ∧
      ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
        phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)) := by
  classical
  obtain ⟨c, -, -, -, -, hPL, hTri, hMO, -⟩ := hk
  obtain ⟨Lseg, hLseg⟩ := PhiLAux.exists_lseg c.seg
  have hInj : LInjective k := GlobalTheory.T.langlands_injective_of_socle PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top c.soc c.jac
  choose Lm hLm using c.ex
  have hLbij : Function.Bijective Lm := by
    refine ⟨fun 𝔪 𝔫 e => hInj 𝔪 𝔫 (Lm 𝔪) (hLm 𝔪) (by rw [e]; exact hLm 𝔫), fun x => ?_⟩
    obtain ⟨𝔪, h𝔪⟩ := c.exh x
    exact ⟨𝔪, PhiLAux.isL_cls_unique c.free (hLm 𝔪) h𝔪⟩
  let L : Multiset (Segment k) ≃ IrrGL (k := k) := Equiv.ofBijective Lm hLbij
  choose hO Δo hΔo using PhiLAux.exists_orderedForm (k := k)
  have hLF : ∀ 𝔪, LFactors 𝔪 (fun a => Lseg (Δo 𝔪 a)) := fun 𝔪 => ⟨Δo 𝔪, hΔo 𝔪, fun _ => hLseg _⟩
  let f : Multiset (Segment k) → IrrGL (k := k) →₀ ℤ := fun 𝔪 =>
    cl0 (prodIrr (fun a => Lseg (Δo 𝔪 a)) (N := ∑ a, (Lseg (Δo 𝔪 a)).1) rfl)
  have hf1 : ∀ 𝔪, f 𝔪 (L 𝔪) = 1 := by
    intro 𝔪
    have hd : ∑ a, (Lseg (Δo 𝔪 a)).1 = (Lm 𝔪).1 :=
      (PhiLAux.lfactors_sum (hLF 𝔪)).trans (PhiLAux.isL_deg (hLm 𝔪)).symm
    show cl0 _ (Lm 𝔪) = 1
    rw [PhiLAux.class_product_irreducible_apply _ _ hd, hMO 𝔪 _ _ _ hd (hLF 𝔪) (hLm 𝔪)]
    rfl
  have hf2 : ∀ 𝔪 𝔫, f 𝔪 (L 𝔫) ≠ 0 →
      msupp 𝔪 = msupp 𝔫 ∧ (𝔪 = 𝔫 ∨ PositivityTheory.Groth.sq 𝔪 < PositivityTheory.Groth.sq 𝔫) := by
    intro 𝔪 𝔫 h0
    by_cases hd : ∑ a, (Lseg (Δo 𝔪 a)).1 = (Lm 𝔫).1
    · refine hTri 𝔪 𝔫 _ _ (Lm 𝔫) hd (hLF 𝔪) (hLm 𝔫) fun e => h0 ?_
      show cl0 _ (Lm 𝔫) = 0
      rw [PhiLAux.class_product_irreducible_apply _ _ hd, e]
      rfl
    · exact absurd (PhiLAux.class_apply_other_degree _ _ (Ne.symm hd)) h0
  obtain ⟨hbij, hinv⟩ := h2 _ _ _ L msupp PositivityTheory.Groth.sq (fun C => Multiset.card C ^ 2) f PhiLAux.sq_le hf1 hf2
  let e : (Segment k →₀ ℕ) ≃ Multiset (Segment k) := (Multiset.toFinsupp (α := Segment k)).symm.toEquiv
  have he : ∀ s, e s = Finsupp.toMultiset s := fun s => by
    show (Multiset.toFinsupp (α := Segment k)).symm s = _
    rw [AddEquiv.symm_apply_eq]
    simp
  let G : MvPolynomial (Segment k) ℤ →+ R k :=
    toR.toAddMonoidHom.comp ((Finsupp.linearCombination ℤ f).toAddMonoidHom.comp ((Finsupp.domCongr (M := ℤ) e).toAddMonoidHom.comp
      (AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)).toAddMonoidHom))
  have hGbij : Function.Bijective G := toR.bijective.comp (hbij.comp ((Finsupp.domCongr e).bijective.comp
    (AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)).bijective))
  have hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)) := by
    intro h N Γ hd
    rw [map_prod, PhiLAux.ring_class_product_irreducible hPL]
    exact Finset.prod_congr rfl fun a _ => phiOf_X _ _
  have hmono : ∀ s : Segment k →₀ ℕ, toR (f (e s)) = s.prod fun n m => toR (sg (Lseg n)) ^ m := by
    intro s
    show toR (cl0 _) = _
    rw [PhiLAux.ring_class_product_irreducible hPL, Finset.prod_eq_multiset_prod,
      ← PhiLAux.prod_map_toMultiset (fun n => toR (sg (Lseg n)))]
    have h1 : Finsupp.toMultiset s = Finset.univ.val.map (Δo (e s)) := (he s).symm.trans (hΔo (e s)).1.symm
    rw [h1, Multiset.map_map]
    rfl
  have hG : ∀ p, phiOf Lseg p = G p := by
    intro p
    refine MvPolynomial.induction_on' p (fun s a => ?_) (fun p q hp hq => ?_)
    · have h1 : G (MvPolynomial.monomial s a) = a • toR (f (e s)) := by
        show toR (Finsupp.linearCombination ℤ f (Finsupp.domCongr e (Finsupp.single s a))) = _
        rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_single, Finsupp.linearCombination_single, map_zsmul]
      rw [h1, hmono, phiOf, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, eq_intCast, ← zsmul_eq_mul]
    · rw [map_add (f := _), map_add (f := _), hp, hq]
  have hphiG : ⇑(phiOf Lseg) = ⇑G := funext hG
  refine ⟨Lseg, hLseg, hphiG ▸ hGbij, fun 𝔫 x hx => ?_, hprod⟩
  obtain ⟨a, ha, hLa⟩ := hinv 𝔫
  have hxL : x = Lm 𝔫 := PhiLAux.isL_cls_unique c.free hx (hLm 𝔫)
  let cE := AddMonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Segment k →₀ ℕ)
  refine ⟨cE.symm ((Finsupp.domCongr e).symm a), ?_, fun s hs => ?_⟩
  · rw [hG]
    show toR (Finsupp.linearCombination ℤ f (Finsupp.domCongr e (cE (cE.symm ((Finsupp.domCongr e).symm a))))) = _
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hLa, hxL]
    rfl
  · rw [MvPolynomial.mem_support_iff] at hs
    have key : a (e s) = ((Finsupp.domCongr e).symm a : (Segment k →₀ ℕ) →₀ ℤ) s := by
      conv_lhs => rw [← AddEquiv.apply_symm_apply (Finsupp.domCongr e) a]
      rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
    rw [← he s]
    exact ha _ (Finsupp.mem_support_iff.2 (by rw [key]; exact hs))

end PositivityTheory.Groth

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZAux
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth.GrothendieckPhiBijection

theorem interleave_perm {T : Type*} {u v w : List T} (h : Zc.Comb.Interleave u v w) : w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm

theorem shuffle_perm {T : Type*} {us : List (List T)} {w : List T} (h : Zc.Comb.Shuffle us w) :
    w.Perm us.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons _ hi ih => rw [List.flatten_cons]; exact (interleave_perm hi).trans (ih.append_left _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem coe_decW (Γ : Segment k) : ((decW Γ : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = Γ.ms := by
  rw [decW, Segment.ms, ← Fin.univ_val_map]
  have : (fun i : Fin Γ.len => Γ.term i.rev) = Γ.term ∘ (Fin.revPerm : Equiv.Perm (Fin Γ.len)) := rfl
  rw [this, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = msupp (L : Multiset (Segment k)) := by
  induction L with
  | nil => simp [msupp]
  | cons Γ L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, coe_decW, ← Multiset.cons_coe, msupp, msupp,
      Multiset.cons_bind]

theorem coe_eq_msupp_of_inShW {𝔫 : Multiset (Segment k)} {w : List (IrrGL (k := k))} (h : InShW 𝔫 w) :
    (w : Multiset (IrrGL (k := k))) = msupp 𝔫 := by
  obtain ⟨L, rfl, hL⟩ := h
  rw [Multiset.coe_eq_coe.2 (shuffle_perm hL), coe_flatten_decW]

theorem msupp_eq_of_isL (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) {𝔫 : Multiset (Segment k)}
    {x : IrrGL (k := k)} (hx : IsL 𝔫 x.rep) (w : List (IrrGL (k := k))) (hc : ∀ c ∈ w, c.IsCusp) (hw : Wd x.rep w) :
    (w : Multiset (IrrGL (k := k))) = msupp 𝔫 := by
  obtain ⟨h, y, hd, ⟨Δ, hΔ, hL⟩, hcos⟩ := hx
  have h1 : Wd (prodIrr y hd) w := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr y hd) hcos.isSubquotient w hw
  have h2 := GlobalTheory.T.segment_product_word_in_shuffle hA hj y hd Δ hL w hc h1
  rw [hΔ.1] at h2
  exact coe_eq_msupp_of_inShW h2

theorem wd_of_jmL_eq_one {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {w : List (IrrGL (k := k))} (h : jmL w π = 1) : Wd π w := by
  unfold jmL at h
  split_ifs at h with hd
  · exact ⟨hd, by rw [h]; exact one_ne_zero⟩
  · exact absurd h zero_ne_one

theorem msupp_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) (hS : JSeg k) (Δ : Segment k)
    {𝔫 : Multiset (Segment k)} (h𝔫 : IsL 𝔫 (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k)))) : msupp 𝔫 = Δ.ms := by
  have hc : ∀ c ∈ List.ofFn Δ.term, c.IsCusp := by
    intro c hc
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hc
    exact Δ.isCusp_term a
  have := msupp_eq_of_isL hA hj h𝔫 (List.ofFn Δ.term) hc (wd_of_jmL_eq_one (hS Z hZ Δ).1)
  rw [← this, Segment.ms, Fin.univ_val_map]

theorem seg_eq_of_ms_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Γ Δ : Segment k} (h : Γ.ms = Δ.ms) : Γ = Δ := _root_.CompanionTheory.Groth.GrothendieckPhiBijection.seg_eq_of_ms_eq (Γ := Γ) (Δ := Δ) hA h

theorem len_lt_of_msupp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} {M : Multiset (Segment k)}
    (hM : msupp M = Δ.ms) (hne : M ≠ {Δ}) : ∀ Γ ∈ M, Γ.len < Δ.len := _root_.CompanionTheory.Groth.GrothendieckPhiBijection.len_lt_of_msupp (Δ := Δ) (M := M) hA hM hne

theorem toMultiset_eq_single_iff (s : Segment k →₀ ℕ) (Δ : Segment k) :
    Finsupp.toMultiset s = {Δ} ↔ s = Finsupp.single Δ 1 := by
  classical
  constructor
  · intro h
    calc s = Multiset.toFinsupp (Finsupp.toMultiset s) := (Finsupp.toMultiset_toFinsupp s).symm
      _ = Multiset.toFinsupp (Finsupp.toMultiset (Finsupp.single Δ 1)) := by
          rw [h, Finsupp.toMultiset_single, one_nsmul]
      _ = Finsupp.single Δ 1 := Finsupp.toMultiset_toFinsupp _
  · rintro rfl
    rw [Finsupp.toMultiset_single, one_nsmul]

theorem prod_X_of_map (s : Segment k →₀ ℕ) {h : ℕ} (Γ : Fin h → Segment k)
    (hΓ : Finset.univ.val.map Γ = Finsupp.toMultiset s) :
    ∏ a, (MvPolynomial.X (Γ a) : MvPolynomial (Segment k) ℤ) = MvPolynomial.monomial s 1 := by
  classical
  have h1 : (Finset.univ.val.map fun a => (MvPolynomial.X (Γ a) : MvPolynomial (Segment k) ℤ)) =
      (Finset.univ.val.map Γ).map MvPolynomial.X := by
    rw [Multiset.map_map]; rfl
  rw [Finset.prod_eq_multiset_prod, h1, hΓ, Finset.prod_multiset_map_count, Finsupp.toFinset_toMultiset]
  simp only [Finsupp.count_toMultiset]
  exact MvPolynomial.prod_X_pow_eq_monomial

theorem exists_enum (s : Segment k →₀ ℕ) :
    ∃ (h : ℕ) (Γ : Fin h → Segment k), Finset.univ.val.map Γ = Finsupp.toMultiset s :=
  ⟨(Finsupp.toMultiset s).toList.length, fun a => (Finsupp.toMultiset s).toList.get a, by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩

def Jh (W : List (IrrGL (k := k))) : GrothGL k →+ ℤ where
  toFun := J W
  map_zero' := Finsupp.sum_zero_index
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

def ell (Δ : Segment k) : GrothGL k →+ ℤ := ∑ S ∈ vSets Δ, (-1 : ℤ) ^ S.card • Jh (vWord Δ S)

theorem ell_apply (Δ : Segment k) (a : GrothGL k) :
    ell Δ a = ∑ S ∈ vSets Δ, (-1 : ℤ) ^ S.card * J (vWord Δ S) a := by
  simp only [ell, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, smul_eq_mul]
  rfl

theorem J_sg (W : List (IrrGL (k := k))) (x : IrrGL (k := k)) : J W (sg x) = ((jmL W x.rep).toNat : ℤ) := by
  unfold J sg
  rw [Finsupp.sum_single_index (zero_mul _), one_mul]

theorem vWord_empty (Δ : Segment k) : vWord Δ ∅ = List.ofFn Δ.term := by
  simp [vWord, List.ofFn_eq_map]

theorem cusp_vWord (Δ : Segment k) (S : Finset (Fin Δ.len)) : ∀ w ∈ vWord Δ S, w.IsCusp := by
  intro w hw
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
  exact Δ.isCusp_term a

theorem ell_sg {Δ : Segment k} {x : IrrGL (k := k)} (h1 : jmL (List.ofFn Δ.term) x.rep = 1)
    (h0 : ∀ S ∈ vSets Δ, S ≠ ∅ → jmL (vWord Δ S) x.rep = 0) : ell Δ (sg x) = 1 := by
  rw [ell_apply, Finset.sum_eq_single (∅ : Finset (Fin Δ.len))]
  · rw [J_sg, vWord_empty, h1]; simp
  · intro S hS hne; rw [J_sg, h0 S hS hne]; simp
  · intro h; exact absurd (by simp [vSets]) h


open Classical in
theorem ell_prod (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL (k := k)) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep) (Δ : Segment k) {h N : ℕ}
    (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N) :
    ell Δ (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)) =
      if Finset.univ.val.map Γ = {Δ} then (-1) ^ (Δ.len - 1) else 0 := by
  have := hAlt Δ h Γ
  rw [ell_apply]
  convert this using 1
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [(hJ (vWord Δ S) N _ (prodIrr (fun a => Lseg (Γ a)) hd) (isSmooth_prodIrr _ hd)
      (GlobalTheory.T.product_irreducible_finite_length hA _ hd)).2,
    GlobalTheory.T.segment_product_jacquet_shuffle_count hA hj Γ (fun a => Lseg (Γ a)) hd (fun i => hL (Γ i)) (vWord Δ S) (cusp_vWord Δ S)]
  simp

theorem vars_lt (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} (p : MvPolynomial (Segment k) ℤ)
    (hp : ∀ s ∈ p.support, msupp (Finsupp.toMultiset s) = Δ.ms) :
    ∀ t ∈ (p - MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1))).vars, t.len < Δ.len := by
  classical
  intro t ht
  obtain ⟨d, hd, htd⟩ := (MvPolynomial.mem_vars_iff_mem_support t).1 ht
  have hcd := MvPolynomial.mem_support_iff.1 hd
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial] at hcd
  have hde : d ≠ Finsupp.single Δ 1 := by
    rintro rfl
    simp at hcd
  rw [if_neg (Ne.symm hde), sub_zero] at hcd
  have hne : Finsupp.toMultiset d ≠ {Δ} := fun h => hde ((toMultiset_eq_single_iff d Δ).1 h)
  exact len_lt_of_msupp hA (hp d (MvPolynomial.mem_support_iff.2 hcd)) hne t ((Finsupp.mem_toMultiset d t).2 htd)

end PositivityTheory.Groth.GrothendieckPhiBijection

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth.GrothendieckPhiBijection

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem ell_phiOf (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL (k := k)) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
    (hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)))
    (Δ : Segment k) (p : MvPolynomial (Segment k) ℤ) :
    ell Δ (toR.symm (phiOf Lseg p)) = p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    obtain ⟨h, Γ, hΓ⟩ := exists_enum u
    have hm : MvPolynomial.monomial u a = MvPolynomial.C a * ∏ i : Fin h, MvPolynomial.X (Γ i) := by
      rw [prod_X_of_map u Γ hΓ, MvPolynomial.C_mul_monomial, mul_one]
    have hC : phiOf Lseg (MvPolynomial.C a) = (a : R k) := by simp [phiOf]
    rw [hm, map_mul, hC, hprod h _ Γ rfl, ← zsmul_eq_mul, map_zsmul, AddEquiv.symm_apply_apply, map_zsmul,
      ell_prod hA hj hJ hAlt Lseg hL Δ Γ rfl, hΓ, MvPolynomial.coeff_C_mul, prod_X_of_map u Γ hΓ,
      MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd ((toMultiset_eq_single_iff u Δ).mp h1) h2
    · exact absurd ((toMultiset_eq_single_iff u Δ).mpr h2) h1
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, MvPolynomial.coeff_add, add_mul]

end PositivityTheory.Groth.GrothendieckPhiBijection

namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]


open GrothendieckPhiBijection in
theorem phiZ_bijective (hk : Steps k) (h1 : TriAut) (h2 : UniTri)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) :
    Function.Bijective (phiOf (k := k) fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
  obtain ⟨Lseg, hL, hbij, hrep, hprod⟩ := phiL_main hk h2
  obtain ⟨hC, -, -, -, -, -, -, -, hJ, hJS, hAlt⟩ := hk
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hx : ∀ Δ : Segment k, ∃ p : MvPolynomial (Segment k) ℤ,
      phiOf Lseg p = toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) ∧
        ∀ s ∈ p.support, msupp (Finsupp.toMultiset s) = Δ.ms := by
    intro Δ
    obtain ⟨n, hn⟩ := hC.exh ⟨Δ.len * Δ.d, Z Δ⟩
    obtain ⟨p, hp1, hp2⟩ := hrep n _ hn
    exact ⟨p, hp1, fun s hs => (hp2 s hs).trans (msupp_seg hA hC.jac Z hZ hJS Δ hn)⟩
  choose p hp1 hp2 using hx
  let ψ : MvPolynomial (Segment k) ℤ →+* MvPolynomial (Segment k) ℤ := (MvPolynomial.aeval p).toRingHom
  have hψX : ∀ Δ, ψ (MvPolynomial.X Δ) = p Δ := fun Δ => MvPolynomial.aeval_X p Δ
  have hcomp : (phiOf Lseg).comp ψ = phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, phiOf]
    · intro Δ
      rw [RingHom.comp_apply, hψX, hp1, phiOf_X]
  have hψ : Function.Bijective ψ := by
    apply h1 (Segment k) (fun Δ => Δ.len) ψ
    intro Δ
    have hell := ell_phiOf hA hC.jac hJ hAlt Lseg hL hprod Δ (p Δ)
    rw [hp1, AddEquiv.symm_apply_apply, ell_sg (hJS Z hZ Δ).1 (hJS Z hZ Δ).2] at hell
    have hc : (p Δ).coeff (Finsupp.single Δ 1) = (-1) ^ (Δ.len - 1) := by
      have h' : ((-1 : ℤ) ^ (Δ.len - 1)) * ((-1) ^ (Δ.len - 1)) = 1 := by
        rw [← mul_pow]
        simp
      calc (p Δ).coeff (Finsupp.single Δ 1)
          = (p Δ).coeff (Finsupp.single Δ 1) * ((-1) ^ (Δ.len - 1) * (-1) ^ (Δ.len - 1)) := by
            rw [h', mul_one]
        _ = (-1) ^ (Δ.len - 1) := by rw [← mul_assoc, ← hell, one_mul]
    refine ⟨(-1) ^ (Δ.len - 1), _, vars_lt hA (p Δ) (hp2 Δ), ?_⟩
    rw [hψX, MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    push_cast
    rw [← hc, add_sub_cancel]
  rw [← hcomp]
  exact hbij.comp hψ

end PositivityTheory.Groth

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth

theorem GrothendieckClassGeneralLinear.class_gl_eq_class {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : HasFiniteLength π) :
    clsGL π h = cl0 π := by
  unfold cl0; rw [dite_eq_left h]

theorem groth_of_steps (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k)
    (h1 : TriAut) (h2 : UniTri) : GlobalTheory.Published.GrothendieckRingPolynomial := by
  intro k _ _ _ _ Z hZ
  obtain ⟨hCls, hMul, hAs, hCo, hOne, hPL, hTri, hMO, hJC, hJS, hAlt⟩ := H k
  haveI : Fact (Assoc k) := ⟨hAs⟩
  haveI : Fact (Comm k) := ⟨hCo⟩
  haveI : Fact (One k) := ⟨hOne⟩
  have hst : Steps k := ⟨hCls, hMul, hAs, hCo, hOne, hPL, hTri, hMO, hJC, hJS, hAlt⟩
  have hbij := phiZ_bijective hst h1 h2 Z hZ
  let e := RingEquiv.ofBijective (phiOf fun Δ : Segment k => (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) hbij
  refine ⟨toR.trans e.symm.toAddEquiv, ?_, ?_, ?_⟩
  · change e.symm (toR (GrothGL.unit k)) = 1
    rw [toR_unit, map_one]
  · intro r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ h
    obtain ⟨_, hc⟩ := hMul r t V W π₁ π₂ h₁ h₂ s₁ s₂
    change e.symm (toR (clsGL (prod₂ π₁ π₂) h)) =
      e.symm (toR (clsGL π₁ h₁)) * e.symm (toR (clsGL π₂ h₂))
    rw [GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, hc, toR_mulR, map_mul]
  · intro Δ
    change e.symm (toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k)))) = MvPolynomial.X Δ
    rw [RingEquiv.symm_apply_eq]
    exact (phiOf_X (fun Δ : Segment k => (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) Δ).symm

end PositivityTheory.Groth

end
