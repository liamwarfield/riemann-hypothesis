module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.SingleEqSmulSingle
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

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

end CompanionTheory.Groth

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

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
  obtain ⟨h₁, -, -, Δ₁, -, -, hΔ₁, -⟩ := GlobalTheory.T.ordered_forms_interleave_sum CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top 𝔪 0
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
  exact class_apply_same_degree _ (GlobalTheory.T.product_irreducible_finite_length CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top x _) c

theorem sum_sq_le (s : Multiset ℕ) : (s.map fun l => l ^ 2).sum ≤ s.sum ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
    have h1 : (a + s.sum) ^ 2 = a ^ 2 + 2 * a * s.sum + s.sum ^ 2 := by ring
    have h2 := Nat.zero_le (2 * a * s.sum)
    rw [h1]
    linarith

theorem sq_le (𝔪 : Multiset (Segment k)) : CompanionTheory.Groth.sq 𝔪 ≤ (Multiset.card (msupp 𝔪)) ^ 2 := by
  have hc : Multiset.card (msupp 𝔪) = (𝔪.map Segment.len).sum := by
    rw [msupp, Multiset.card_bind]
    simp [Segment.card_ms]
  have hs : CompanionTheory.Groth.sq 𝔪 = ((𝔪.map Segment.len).map fun l => l ^ 2).sum := by
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
  have hInj : LInjective k := GlobalTheory.T.langlands_injective_of_socle CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top c.soc c.jac
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
      msupp 𝔪 = msupp 𝔫 ∧ (𝔪 = 𝔫 ∨ CompanionTheory.Groth.sq 𝔪 < CompanionTheory.Groth.sq 𝔫) := by
    intro 𝔪 𝔫 h0
    by_cases hd : ∑ a, (Lseg (Δo 𝔪 a)).1 = (Lm 𝔫).1
    · refine hTri 𝔪 𝔫 _ _ (Lm 𝔫) hd (hLF 𝔪) (hLm 𝔫) fun e => h0 ?_
      show cl0 _ (Lm 𝔫) = 0
      rw [PhiLAux.class_product_irreducible_apply _ _ hd, e]
      rfl
    · exact absurd (PhiLAux.class_apply_other_degree _ _ (Ne.symm hd)) h0
  obtain ⟨hbij, hinv⟩ := h2 _ _ _ L msupp CompanionTheory.Groth.sq (fun C => Multiset.card C ^ 2) f PhiLAux.sq_le hf1 hf2
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

end CompanionTheory.Groth

end
