module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolUnitNeZero
noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam

def polUnit (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [single]⟩

@[simp] theorem polUnit_coe (d : ℕ) :
    ((polUnit d : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) = single (Sum.inl 0) (Sum.inr 0) 1 :=
  rfl

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickActionsIsomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickActionsIsomorphic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.ZarhinUniqIso

open Matrix

variable {S : Scheme.{0}}

theorem mulA_flat_surjective_qc (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (n : ℕ) (hn : 1 ≤ n) :
    Flat ((𝟙 A) ^ n : A ⟶ A).left ∧ Surjective ((𝟙 A) ^ n : A ⟶ A).left ∧
      QuasiCompact ((𝟙 A) ^ n : A ⟶ A).left := by
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA n hn
  have e : ((𝟙 A) ^ n : A ⟶ A) = ReciprocityTheory.ChartRestriction.G.Out.mulA A n := rfl
  rw [e]
  refine ⟨h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_, inferInstance⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2

def preHom {X Y M : Over S} [GrpObj M] (f : X ⟶ Y) : (Y ⟶ M) →* (X ⟶ M) :=
  MonoidHom.mk' (fun g => f ≫ g) (fun a b => MonObj.comp_mul f a b)

def postHom {X M N : Over S} [GrpObj M] [GrpObj N] (g : M ⟶ N) [IsMonHom g] : (X ⟶ M) →* (X ⟶ N) :=
  MonoidHom.mk' (fun f => f ≫ g) (fun a b => MonObj.mul_comp a b g)

theorem comp_zpow' {X Y M : Over S} [GrpObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℤ) : f ≫ g ^ n = (f ≫ g) ^ n :=
  map_zpow (preHom f) g n

theorem zpow_comp' {X M N : Over S} [GrpObj M] [GrpObj N] (f : X ⟶ M) (g : M ⟶ N) [IsMonHom g] (n : ℤ) :
    (f ^ n) ≫ g = (f ≫ g) ^ n :=
  map_zpow (postHom (X := X) g) f n

theorem comp_npow' {X Y M : Over S} [GrpObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℕ) : f ≫ g ^ n = (f ≫ g) ^ n :=
  map_pow (preHom f) g n

theorem npow_comp' {X M N : Over S} [GrpObj M] [GrpObj N] (f : X ⟶ M) (g : M ⟶ N) [IsMonHom g] (n : ℕ) :
    (f ^ n) ≫ g = (f ≫ g) ^ n :=
  map_pow (postHom (X := X) g) f n

theorem comp_prod' {X Y M : Over S} [GrpObj M] [IsCommMonObj M] {J : Type} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ (∏ i ∈ s, g i) = ∏ i ∈ s, (f ≫ g i) :=
  map_prod (preHom f) g s

theorem prod_comp' {X M N : Over S} [GrpObj M] [IsCommMonObj M] [GrpObj N] [IsCommMonObj N] {J : Type}
    (s : Finset J) (f : J → (X ⟶ M)) (g : M ⟶ N) [IsMonHom g] : (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, (f i ≫ g) :=
  map_prod (postHom (X := X) g) f s

end GlobalTheory.ZarhinUniqIso

noncomputable section

namespace GlobalTheory.ZarhinUniqIso

open Matrix GlobalTheory.ZarhinFam

variable {S : Scheme.{0}}

section Act

variable {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A] {act : O → (A ⟶ A)}

theorem act_zero' (h : IsRAct A act) : act 0 = 1 := by
  have e := h.2.2.2 0 0
  rw [add_zero] at e
  exact (mul_eq_left.1 e.symm)

def ahom (h : IsRAct A act) : O →+ Additive (A ⟶ A) where
  toFun a := Additive.ofMul (act a)
  map_zero' := by rw [act_zero' h]; rfl
  map_add' a b := by rw [h.2.2.2]; rfl

theorem act_sum' (h : IsRAct A act) {J : Type} (s : Finset J) (f : J → O) :
    act (∑ i ∈ s, f i) = ∏ i ∈ s, act (f i) := by
  have := map_sum (ahom h) f s
  exact congrArg Additive.toMul this

theorem act_zsmul' (h : IsRAct A act) (n : ℤ) (a : O) : act (n • a) = act a ^ n := by
  have := map_zsmul (ahom h) n a
  exact congrArg Additive.toMul this

end Act

def lo (d : ℕ) (k : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨(d : ℤ) • single k (Sum.inl 0) 1, fun i j => by
    simp only [Matrix.smul_apply, single_apply, smul_eq_mul]
    split_ifs <;> simp⟩

def up (d : ℕ) (k : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨single (Sum.inl 0) k 1, fun i j => by simp [single_apply]⟩

def ecol (d : ℕ) (k : Fin 4 ⊕ Fin 4) (i : Fin 4) : ord d :=
  ⟨single k (Sum.inr i) 1, fun a b => by simp [single_apply]⟩

def erow (d : ℕ) (i : Fin 4) (l : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨single (Sum.inl i) l 1, fun a b => by simp [single_apply]⟩

theorem lo_inl (d : ℕ) (i : Fin 4) : lo d (Sum.inl i) = (d : ℤ) • erow d i (Sum.inl 0) := by
  ext1; ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

theorem up_inr (d : ℕ) (i : Fin 4) : up d (Sum.inr i) = polUnit d * ecol d (Sum.inr 0) i := by
  ext1; ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

theorem lo_idem_pol (d : ℕ) (k : Fin 4 ⊕ Fin 4) : lo d k * idem d * polUnit d = (d : ℤ) • ecol d k 0 := by
  ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

theorem lo_idem_up_sum (d : ℕ) : ∑ k, lo d k * idem d * up d k = (d : ℤ) • (1 : ord d) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul, OneMemClass.coe_one]
  ext a b
  rw [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

theorem idem_lo (d : ℕ) (k : Fin 4 ⊕ Fin 4) : idem d * lo d k = if k = Sum.inl 0 then (d : ℤ) • idem d else 0 := by
  split_ifs with hk
  · subst hk; ext1; ext a b; rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]
  · ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try (intros; subst_vars; simp_all))

theorem zarhinOrderUpperMatrixUnit_inl_zero (d : ℕ) : up d (Sum.inl 0) = idem d := rfl

theorem mul_lo (d : ℕ) (o : ord d) (k : Fin 4 ⊕ Fin 4) :
    o * lo d k = ∑ j, (o : Matrix _ _ ℤ) j k • lo d j := by
  ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

theorem up_mul (d : ℕ) (o : ord d) (k : Fin 4 ⊕ Fin 4) :
    up d k * o = ∑ j, (o : Matrix _ _ ℤ) k j • up d j := by
  ext1; ext a b; rcases k with k | k <;> rcases a with a | a <;> rcases b with b | b <;> simp [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel] <;> (try split_ifs) <;> simp_all [-zsmul_eq_mul, -nsmul_eq_mul, AddSubgroupClass.coe_zsmul, AddSubmonoidClass.coe_finsetSum, Matrix.smul_apply, Matrix.one_apply, lo, up, idem, ecol, erow, polUnit, Matrix.mul_apply, single_apply, Fintype.sum_sum_type, Matrix.sum_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]

end GlobalTheory.ZarhinUniqIso

noncomputable section

namespace GlobalTheory.ZarhinUniqIso

open Matrix GlobalTheory.ZarhinFam

variable {S : Scheme.{0}}

theorem mulA_comm {X Y : Over S} [GrpObj X] [GrpObj Y] (g : X ⟶ Y) [IsMonHom g] (n : ℕ) :
    ((𝟙 X) ^ n) ≫ g = g ≫ (𝟙 Y) ^ n := by
  rw [npow_comp', comp_npow', Category.id_comp, Category.comp_id]

theorem pow_kill {T X M : Over S} [GrpObj X] [GrpObj M] (x : T ⟶ X) (g : X ⟶ M) [IsMonHom g] (d : ℕ)
    (hx : x ≫ (𝟙 X) ^ d = 1) : x ≫ g ^ (d : ℤ) = 1 := by
  have h : x ^ d = 1 := by rw [← hx, comp_npow', Category.comp_id]
  rw [comp_zpow', zpow_natCast, ← npow_comp', h, MonObj.one_comp]

section Main

variable {A Z₁ Z₂ : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj Z₁] [IsCommMonObj Z₁] [GrpObj Z₂]
  [IsCommMonObj Z₂] {d : ℕ} {act₁ : ord d → (Z₁ ⟶ Z₁)} {act₂ : ord d → (Z₂ ⟶ Z₂)}

def dMap (d : ℕ) (act₁ : ord d → (Z₁ ⟶ Z₁)) (act₂ : ord d → (Z₂ ⟶ Z₂)) (pr₁ : Z₁ ⟶ A) (inc₂ : A ⟶ Z₂) :
    Z₁ ⟶ Z₂ :=
  ∏ k, act₁ (lo d k) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)

theorem isMonHom_dMap (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₂ : A ⟶ Z₂)
    [IsMonHom pr₁] [IsMonHom inc₂] : IsMonHom (dMap d act₁ act₂ pr₁ inc₂) := by
  haveI := h₁.1; haveI := h₂.1
  exact Finset.prod_induction _ (fun x => IsMonHom x)
    (fun x y hx hy => by haveI := hx; haveI := hy; exact GlobalTheory.Serre.isMonHom_mul x y)
    GlobalTheory.Serre.isMonHom_one (fun k _ => inferInstance)

theorem dMap_lin (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₂ : A ⟶ Z₂)
    [IsMonHom pr₁] [IsMonHom inc₂] (o : ord d) :
    act₁ o ≫ dMap d act₁ act₂ pr₁ inc₂ = dMap d act₁ act₂ pr₁ inc₂ ≫ act₂ o := by
  haveI := h₁.1; haveI := h₂.1
  unfold dMap
  rw [comp_prod', prod_comp']
  have L : ∀ k, act₁ o ≫ act₁ (lo d k) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k) =
      ∏ j, (act₁ (lo d j) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)) ^ ((o : Matrix _ _ ℤ) j k) := by
    intro k
    rw [← Category.assoc, ← h₁.2.2.1, mul_lo, act_sum' h₁, prod_comp']
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [act_zsmul' h₁, zpow_comp']
  have R : ∀ j, (act₁ (lo d j) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d j)) ≫ act₂ o =
      ∏ k, (act₁ (lo d j) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)) ^ ((o : Matrix _ _ ℤ) j k) := by
    intro j
    simp only [Category.assoc]
    rw [← h₂.2.2.1, up_mul, act_sum' h₂]
    simp only [act_zsmul' h₂, comp_prod', comp_zpow']
  simp_rw [L, R]
  exact Finset.prod_comm

theorem dMap_kill (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₁ : A ⟶ Z₁) (inc₂ : A ⟶ Z₂)
    [IsMonHom pr₁] [IsMonHom inc₁] [IsMonHom inc₂] (hpi₁ : pr₁ ≫ inc₁ = act₁ (idem d))
    (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ inc₁ ≫ act₁ (polUnit d) = 1 → x ≫ inc₂ ≫ act₂ (polUnit d) = 1)
    (T : Over S) (x : T ⟶ Z₁) (hx : x ≫ (𝟙 Z₁) ^ d = 1) : x ≫ dMap d act₁ act₂ pr₁ inc₂ = 1 := by
  haveI := h₁.1; haveI := h₂.1
  unfold dMap
  rw [comp_prod']
  refine Finset.prod_eq_one fun k _ => ?_
  rcases k with i | i
  · rw [lo_inl, act_zsmul' h₁, ← Category.assoc, pow_kill x _ d hx, MonObj.one_comp]
  · have h0 : (x ≫ act₁ (lo d (Sum.inr i)) ≫ pr₁) ≫ inc₁ ≫ act₁ (polUnit d) = 1 := by
      simp only [Category.assoc]
      rw [reassoc_of% hpi₁, ← h₁.2.2.1, ← h₁.2.2.1, ← _root_.mul_assoc, lo_idem_pol, act_zsmul' h₁, pow_kill x _ d hx]
    have h1 := hker T _ h0
    calc x ≫ act₁ (lo d (Sum.inr i)) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inr i))
        = ((x ≫ act₁ (lo d (Sum.inr i)) ≫ pr₁) ≫ inc₂ ≫ act₂ (polUnit d)) ≫ act₂ (ecol d (Sum.inr 0) i) := by
          rw [up_inr, h₂.2.2.1]; simp only [Category.assoc]
      _ = 1 := by rw [h1, MonObj.one_comp]

theorem inc_dMap (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₁ : A ⟶ Z₁) (pr₂ : Z₂ ⟶ A)
    (inc₂ : A ⟶ Z₂) [IsMonHom pr₁] [IsMonHom inc₁] [IsMonHom inc₂] [IsMonHom pr₂]
    (hip₁ : inc₁ ≫ pr₁ = 𝟙 A) (hpi₁ : pr₁ ≫ inc₁ = act₁ (idem d))
    (hip₂ : inc₂ ≫ pr₂ = 𝟙 A) (hpi₂ : pr₂ ≫ inc₂ = act₂ (idem d)) :
    inc₁ ≫ dMap d act₁ act₂ pr₁ inc₂ = ((𝟙 A) ^ d) ≫ inc₂ := by
  haveI := h₁.1; haveI := h₂.1
  have hi : inc₁ = inc₁ ≫ act₁ (idem d) := by rw [← hpi₁, reassoc_of% hip₁]
  have hW : act₁ (idem d) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0)) = pr₁ ≫ inc₂ := by
    rw [zarhinOrderUpperMatrixUnit_inl_zero, ← hpi₂, ← hpi₁]; simp only [Category.assoc]; rw [reassoc_of% hip₁, reassoc_of% hip₂]
  unfold dMap
  rw [comp_prod', Finset.prod_eq_single (Sum.inl 0)]
  · calc inc₁ ≫ act₁ (lo d (Sum.inl 0)) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0))
        = inc₁ ≫ act₁ (idem d * lo d (Sum.inl 0)) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0)) := by
          rw [h₁.2.2.1]; conv_lhs => rw [hi]
          simp only [Category.assoc]
      _ = inc₁ ≫ (act₁ (idem d) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d (Sum.inl 0))) ^ (d : ℤ) := by
          rw [idem_lo, if_pos rfl, act_zsmul' h₁, zpow_comp']
      _ = ((𝟙 A) ^ d) ≫ inc₂ := by
          rw [hW, comp_zpow', reassoc_of% hip₁, zpow_natCast, npow_comp', Category.id_comp]
  · intro k _ hk
    rw [hi, Category.assoc, ← Category.assoc (act₁ (idem d)), ← h₁.2.2.1, idem_lo, if_neg hk, act_zero' h₁,
      MonObj.one_comp, MonObj.comp_one]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lin_of_dMap (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₂ : A ⟶ Z₂)
    [IsMonHom pr₁] [IsMonHom inc₂] (e : Z₁ ⟶ Z₂) [Epi ((𝟙 Z₁) ^ d)]
    (hf : ((𝟙 Z₁) ^ d) ≫ e = dMap d act₁ act₂ pr₁ inc₂) (o : ord d) : act₁ o ≫ e = e ≫ act₂ o := by
  haveI := h₁.1
  rw [← cancel_epi ((𝟙 Z₁) ^ d), ← Category.assoc, mulA_comm, Category.assoc, hf, reassoc_of% hf,
    dMap_lin h₁ h₂]

theorem inc_of_dMap (h₁ : IsRAct Z₁ act₁) (h₂ : IsRAct Z₂ act₂) (pr₁ : Z₁ ⟶ A) (inc₁ : A ⟶ Z₁) (pr₂ : Z₂ ⟶ A)
    (inc₂ : A ⟶ Z₂) [IsMonHom pr₁] [IsMonHom inc₁] [IsMonHom inc₂] [IsMonHom pr₂]
    (hip₁ : inc₁ ≫ pr₁ = 𝟙 A) (hpi₁ : pr₁ ≫ inc₁ = act₁ (idem d))
    (hip₂ : inc₂ ≫ pr₂ = 𝟙 A) (hpi₂ : pr₂ ≫ inc₂ = act₂ (idem d)) (e : Z₁ ⟶ Z₂) [Epi ((𝟙 A) ^ d)]
    (hf : ((𝟙 Z₁) ^ d) ≫ e = dMap d act₁ act₂ pr₁ inc₂) : inc₁ ≫ e = inc₂ := by
  rw [← cancel_epi ((𝟙 A) ^ d), ← Category.assoc, mulA_comm, Category.assoc, hf,
    inc_dMap h₁ h₂ pr₁ inc₁ pr₂ inc₂ hip₁ hpi₁ hip₂ hpi₂]

theorem inv_of_dMap (h₁ : IsRAct Z₁ act₁) (pr₁ : Z₁ ⟶ A) (inc₁ : A ⟶ Z₁) (inc₂ : A ⟶ Z₂)
    (hpi₁ : pr₁ ≫ inc₁ = act₁ (idem d)) (e₁₂ : Z₁ ⟶ Z₂) (e₂₁ : Z₂ ⟶ Z₁) [IsMonHom e₂₁] [Epi ((𝟙 Z₁) ^ d)]
    (hf : ((𝟙 Z₁) ^ d) ≫ e₁₂ = dMap d act₁ act₂ pr₁ inc₂) (hlin : ∀ o, act₂ o ≫ e₂₁ = e₂₁ ≫ act₁ o)
    (hinc : inc₂ ≫ e₂₁ = inc₁) : e₁₂ ≫ e₂₁ = 𝟙 Z₁ := by
  rw [← cancel_epi ((𝟙 Z₁) ^ d), reassoc_of% hf, Category.comp_id]
  unfold dMap
  rw [prod_comp']
  have key : ∀ k, (act₁ (lo d k) ≫ pr₁ ≫ inc₂ ≫ act₂ (up d k)) ≫ e₂₁ = act₁ (lo d k * idem d * up d k) := by
    intro k
    simp only [Category.assoc]
    rw [hlin, reassoc_of% hinc, reassoc_of% hpi₁, h₁.2.2.1, h₁.2.2.1, Category.assoc]
  simp_rw [key]
  rw [← act_sum' h₁, lo_idem_up_sum, act_zsmul' h₁, h₁.2.1, zpow_natCast]

end Main

end GlobalTheory.ZarhinUniqIso

namespace GlobalTheory.ZarhinUniqIso

open GlobalTheory.ZarhinFam

theorem zarhin_uniq_iso : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)) (inc₁ : c.A ⟶ z₁.A) (pr₁ : z₁.A ⟶ c.A) (inc₂ : c.A ⟶ z₂.A) (pr₂ : z₂.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → IsMonHom inc₁ → IsMonHom pr₁ → inc₁ ≫ pr₁ = 𝟙 c.A → pr₁ ≫ inc₁ = act₁ (GlobalTheory.ZarhinFam.idem d) → IsMonHom inc₂ → IsMonHom pr₂ → inc₂ ≫ pr₂ = 𝟙 c.A → pr₂ ≫ inc₂ = act₂ (GlobalTheory.ZarhinFam.idem d) → (∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔ x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1) → ∃ e : z₁.A ≅ z₂.A, IsMonHom e.hom ∧ inc₁ ≫ e.hom = inc₂ ∧ ∀ o, act₁ o ≫ e.hom = e.hom ≫ act₂ o := by
  intro h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ pr₂ _hu h₁ h₂ hinc₁ hpr₁ hip₁ hpi₁ hinc₂ hpr₂ hip₂ hpi₂ hker
  have hd1 : 1 ≤ d := hd
  obtain ⟨fZ₁, sZ₁, qZ₁⟩ := mulA_flat_surjective_qc z₁.A z₁.ab d hd1
  obtain ⟨fZ₂, sZ₂, qZ₂⟩ := mulA_flat_surjective_qc z₂.A z₂.ab d hd1
  obtain ⟨fA, sA, qA⟩ := mulA_flat_surjective_qc c.A c.ab d hd1
  have m₁ : IsMonHom ((𝟙 z₁.A) ^ d) := GlobalTheory.AbLaw.MulN.isMonHom_mulA z₁.A d
  have m₂ : IsMonHom ((𝟙 z₂.A) ^ d) := GlobalTheory.AbLaw.MulN.isMonHom_mulA z₂.A d
  have mA : IsMonHom ((𝟙 c.A) ^ d) := GlobalTheory.AbLaw.MulN.isMonHom_mulA c.A d
  obtain ⟨⟨e₁₂, he₁₂, hf₁₂⟩, epi₁⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective S z₁.A z₁.A z₂.A
    ((𝟙 z₁.A) ^ d) (dMap d act₁ act₂ pr₁ inc₂) m₁ (isMonHom_dMap h₁ h₂ pr₁ inc₂) fZ₁ sZ₁ qZ₁
    (dMap_kill h₁ h₂ pr₁ inc₁ inc₂ hpi₁ (fun T x => (hker T x).1))
  obtain ⟨⟨e₂₁, he₂₁, hf₂₁⟩, epi₂⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective S z₂.A z₂.A z₁.A
    ((𝟙 z₂.A) ^ d) (dMap d act₂ act₁ pr₂ inc₁) m₂ (isMonHom_dMap h₂ h₁ pr₂ inc₁) fZ₂ sZ₂ qZ₂
    (dMap_kill h₂ h₁ pr₂ inc₂ inc₁ hpi₂ (fun T x => (hker T x).2))
  have epiA := (GlobalTheory.exists_monHom_factor_of_flat_surjective S c.A c.A c.A ((𝟙 c.A) ^ d) ((𝟙 c.A) ^ d) mA mA
    fA sA qA (fun _ _ hx => hx)).2
  have lin₁₂ := lin_of_dMap h₁ h₂ pr₁ inc₂ e₁₂ hf₁₂
  have lin₂₁ := lin_of_dMap h₂ h₁ pr₂ inc₁ e₂₁ hf₂₁
  have inc₁₂ := inc_of_dMap h₁ h₂ pr₁ inc₁ pr₂ inc₂ hip₁ hpi₁ hip₂ hpi₂ e₁₂ hf₁₂
  have inc₂₁ := inc_of_dMap h₂ h₁ pr₂ inc₂ pr₁ inc₁ hip₂ hpi₂ hip₁ hpi₁ e₂₁ hf₂₁
  refine ⟨⟨e₁₂, e₂₁, ?_, ?_⟩, he₁₂, inc₁₂, lin₁₂⟩
  · exact inv_of_dMap h₁ pr₁ inc₁ inc₂ hpi₁ e₁₂ e₂₁ hf₁₂ lin₂₁ inc₂₁
  · exact inv_of_dMap h₂ pr₂ inc₂ inc₁ hpi₂ e₂₁ e₁₂ hf₂₁ lin₁₂ inc₁₂

end GlobalTheory.ZarhinUniqIso
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickActionsIsomorphicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTrick_actions_isomorphic : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)) (inc₁ : c.A ⟶ z₁.A) (pr₁ : z₁.A ⟶ c.A) (inc₂ : c.A ⟶ z₂.A) (pr₂ : z₂.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → IsMonHom inc₁ → IsMonHom pr₁ → inc₁ ≫ pr₁ = 𝟙 c.A → pr₁ ≫ inc₁ = act₁ (GlobalTheory.ZarhinFam.idem d) → IsMonHom inc₂ → IsMonHom pr₂ → inc₂ ≫ pr₂ = 𝟙 c.A → pr₂ ≫ inc₂ = act₂ (GlobalTheory.ZarhinFam.idem d) → (∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔ x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1) → ∃ e : z₁.A ≅ z₂.A, IsMonHom e.hom ∧ inc₁ ≫ e.hom = inc₂ ∧ ∀ o, act₁ o ≫ e.hom = e.hom ≫ act₂ o := by
  first | (exact @GlobalTheory.ZarhinUniqIso.zarhin_uniq_iso) | (exact GlobalTheory.ZarhinUniqIso.zarhin_uniq_iso) | (intros; apply GlobalTheory.ZarhinUniqIso.zarhin_uniq_iso  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickBundleUniqueOfOrderLinearIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickBundleUniqueOfOrderLinearIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZarhinUniqBundle

variable {S : Scheme.{0}} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}

theorem evc_symm (o : SiegPre h M ζ s) {Y : Over S} (a b : Y ⟶ o.A) :
    evc o.isLB a b = evc o.isLB b a := by
  have hs : (swap o.P).IsLB := pull_isLB o.isLB _
  have c : cls o.P o.isLB = cls (swap o.P) hs := (cls_eq_iff o.isLB hs).2 o.symm
  rw [← evc_swap o.isLB hs b a]
  simp only [evc, c]

theorem additive (o : SiegPre h M ζ s) : IsAdditive o.P ∧ IsAdditive (swap o.P) :=
  additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab o.isLB o.rig₁ o.rig₂

theorem evc_mul_left (o : SiegPre h M ζ s) {Y : Over S} (a a' b : Y ⟶ o.A) :
    evc o.isLB (a * a') b = evc o.isLB a b + evc o.isLB a' b :=
  (isAdditive_iff o.isLB).1 (additive o).1 Y a a' b

theorem evc_mul_right (o : SiegPre h M ζ s) {Y : Over S} (a b b' : Y ⟶ o.A) :
    evc o.isLB a (b * b') = evc o.isLB a b + evc o.isLB a b' := by
  rw [evc_symm o a, evc_symm o a, evc_symm o a]; exact evc_mul_left o _ _ _

theorem isPerfect (o : SiegPre h M ζ s) (hp : o.Principal) : IsPerfect o.A o.A o.P := by
  refine ⟨o.isLB, o.rig₁, o.rig₂, fun T x hx ↦ hp.2 T x ?_, fun T x hx ↦ hp.2 T x ?_⟩
  · have e := congrArg (pull (lift (snd o.A T) (fst o.A T)).left) ((triv_ev_iff o.isLB _ _).1 hx)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
    exact (triv_ev_iff o.isLB _ _).2 e
  · have e := (triv_ev_iff o.isLB _ _).1 hx
    rw [evc_symm o] at e
    exact (triv_ev_iff o.isLB _ _).2 e

end GlobalTheory.ZarhinUniqBundle

namespace GlobalTheory.ZarhinUniqBundle

open Matrix GlobalTheory.ZarhinFam

def colU (d : ℕ) (k : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨(d : ℤ) • single k (Sum.inl 0) 1, fun i j ↦ by rw [Matrix.smul_apply, smul_eq_mul]; exact dvd_mul_right _ _⟩

def rowU (d : ℕ) (k : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨single (Sum.inl 0) k 1, fun i j ↦ by simp [single]⟩

theorem natCast_eq_sum (d : ℕ) : ((d : ℕ) : ord d) = ∑ k, colU d k * idem d * rowU d k := by
  apply Subtype.ext
  have hs : ((∑ k, colU d k * idem d * rowU d k : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      ∑ k, (colU d k : Matrix _ _ ℤ) * (idem d : Matrix _ _ ℤ) * (rowU d k : Matrix _ _ ℤ) := by
    simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
  rw [hs]
  ext i j
  simp only [colU, rowU, idem, Matrix.smul_mul, single_mul_single_same, _root_.mul_one, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, SubringClass.coe_natCast, Matrix.natCast_apply, single_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hx : ∀ x : Fin 4 ⊕ Fin 4, ¬ (x = i ∧ x = j) := fun x hx ↦ hij (hx.1.symm.trans hx.2)
    simp [hij, hx]

end GlobalTheory.ZarhinUniqBundle

namespace GlobalTheory.ZarhinUniqBundle


open ReciprocityTheory.ChartRestriction.G.Out in
theorem cancel_pow : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B], IsAbelianScheme A → ∀ d : ℕ, 0 < d →
    ∀ f g : A ⟶ B, (𝟙 A ^ d) ≫ f = (𝟙 A ^ d) ≫ g → f = g := by
  intro S A B _ _ hA d hd f g hfg
  have hc := hA.comm
  obtain ⟨hfin, hfl⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA d hd
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA A d
  have hsurj : Surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A d).left :=
    GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t ↦ by
      letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
      exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd gi K _ (ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA) _
        inferInstance
        (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hfin)).2
  exact GlobalTheory.DivisibleHom.cancel_of_flat_surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A d) hfg

end GlobalTheory.ZarhinUniqBundle

namespace GlobalTheory.ZarhinUniqBundle

theorem isDual_of_isPerfect : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), IsPerfect A A P → IsAdditive P → IsAdditive (swap P) → IsDual A A P := by
  intro S A _ hA P hP a₁ a₂
  obtain ⟨D, _, Q, hD', -, q, q'⟩ := GlobalTheory.dualAbelianScheme S A hA
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP.isLB a₁ a₂
  have ix : IsIso x := isIso_of_isIso_pullback hA hD' x fun Ω _ _ s ↦ by
    letI : GrpObj ((Over.pullback s).obj A) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback s).obj D) := Functor.grpObjObj
    have f := isGrpPullback_pullback A s
    have d := isGrpPullback_pullback D s
    have hA₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA f
    have := hA₀.comm
    obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim Ω _ hA₀
    obtain ⟨m', m'₁, m'₂⟩ := exists_prod_pullback f f
    have hP₀ := pull_isLB hP.isLB m'
    have p₀ := GlobalTheory.PerfectDual.isDual_of_isPerfect GlobalTheory.dualAbelianScheme _ _ hA₀ hA₀ hg hg
      (hP.baseChange f f m'₁ m'₂ hP₀ ((cls_eq_iff hP₀ hP₀).1 rfl))
    obtain ⟨m, m₁, m₂⟩ := exists_prod_pullback f d
    have hQ := pull_isLB q.isLB m
    have q₀ := q.baseChange f d m₁ m₂ hQ ((cls_eq_iff hQ hQ).1 rfl)
    refine p₀.isIso_of_cls q₀ ?_
    rw [cls_pull hP.isLB _ hP₀, e]
    exact GlobalTheory.BirigidLift.pull_evc_eq m'₁ m'₂ m₁ m₂ q.isLB hQ (x := x) (pullback.lift_fst _ _ _).symm
  exact isDual_of_iso S A A D P Q q hP.isLB x ix hx ((cls_eq_iff hP.isLB (pull_isLB q.isLB _)).1 e)

end GlobalTheory.ZarhinUniqBundle

namespace GlobalTheory.ZarhinUniqBundle

open GlobalTheory.ZarhinFam

section Act

variable {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A] {act : O → (A ⟶ A)}

theorem act_zero (hr : IsRAct A act) : act 0 = 1 := by
  have e := hr.2.2.2 0 0
  rw [add_zero] at e
  exact (mul_eq_left.1 e.symm)

theorem act_natCast (hr : IsRAct A act) (n : ℕ) : act (n : O) = 𝟙 A ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero hr, pow_zero]
  | succ n ih => rw [Nat.cast_succ, hr.2.2.2, ih, hr.2.1, pow_succ]

theorem act_sum (hr : IsRAct A act) {κ : Type} (s : Finset κ) (f : κ → O) :
    act (∑ i ∈ s, f i) = ∏ i ∈ s, act (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, act_zero hr]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hr.2.2.2, ih]

end Act

theorem prod_comp {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    {κ : Type} (s : Finset κ) (f : κ → (A ⟶ A)) (u : A ⟶ B) [IsMonHom u] :
    (∏ i ∈ s, f i) ≫ u = ∏ i ∈ s, (f i ≫ u) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem evc_adj {S : Scheme.{0}} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} {O : Type} [Ring O]
    (o : SiegPre h M ζ s) {bar' : O → O} {act : O → (o.A ⟶ o.A)} (ha : Adj o.A o.P bar' act) (a : O)
    {Y : Over S} (x y : Y ⟶ o.A) : evc o.isLB (x ≫ act a) y = evc o.isLB x (y ≫ act (bar' a)) := by
  have h1 := pull_isLB o.isLB (lift (fst o.A o.A ≫ act a) (snd o.A o.A)).left
  have h2 := pull_isLB o.isLB (lift (fst o.A o.A) (snd o.A o.A ≫ act (bar' a))).left
  have c := (cls_eq_iff h1 h2).2 (ha a)
  have k := congrArg (pull (lift x y).left) c
  rw [cls_pull o.isLB _ h1, cls_pull o.isLB _ h2, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left,
    comp_lift, comp_lift, lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc] at k
  exact k

theorem lbIso_of_ordLinear : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)) (inc₁ : c.A ⟶ z₁.A) (pr₁ : z₁.A ⟶ c.A) (inc₂ : c.A ⟶ z₂.A) (e : z₁.A ≅ z₂.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → IsMonHom inc₁ → IsMonHom pr₁ → inc₁ ≫ pr₁ = 𝟙 c.A → pr₁ ≫ inc₁ = act₁ (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z₁.P.pull (inc₁ ⊗ₘ inc₁).left) → LBIso c.P (z₂.P.pull (inc₂ ⊗ₘ inc₂).left) → IsMonHom e.hom → inc₁ ≫ e.hom = inc₂ → (∀ o, act₁ o ≫ e.hom = e.hom ≫ act₂ o) → LBIso z₁.P (z₂.P.pull (e.hom ⊗ₘ e.hom).left) := by
  intro h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ e hdu hker hp₁ hp₂ hr₁ hr₂ ha₁ ha₂ hi hpr hip hpi hc₁ hc₂
    he hinc hact
  have hL₁ := z₁.isLB
  have hL₂ := z₂.isLB
  have hD : IsDual z₁.A z₁.A z₁.P :=
    isDual_of_isPerfect S z₁.A z₁.ab z₁.P (isPerfect z₁ hp₁) (additive z₁).1 (additive z₁).2
  have hP' : (z₂.P.pull (e.hom ⊗ₘ e.hom).left).IsLB := pull_isLB hL₂ _
  have K' : ∀ (Y : Over S) (a b : Y ⟶ z₁.A), evc hP' a b = evc hL₂ (a ≫ e.hom) (b ≫ e.hom) := by
    intro Y a b
    rw [evc, evc, cls_pull hL₂ _ hP', ← pull_comp, ← Over.comp_left, lift_map]
  have hs' : (swap (z₂.P.pull (e.hom ⊗ₘ e.hom).left)).IsLB := pull_isLB hP' _
  have addP' : IsAdditive (z₂.P.pull (e.hom ⊗ₘ e.hom).left) := (isAdditive_iff hP').2 fun Y a a' b ↦ by
    rw [K', K', K', MonObj.mul_comp]; exact evc_mul_left z₂ _ _ _
  have addP's : IsAdditive (swap (z₂.P.pull (e.hom ⊗ₘ e.hom).left)) := (isAdditive_iff hs').2 fun Y b b' a ↦ by
    rw [evc_swap hP' hs', evc_swap hP' hs', evc_swap hP' hs', K', K', K', MonObj.mul_comp]
    exact evc_mul_right z₂ _ _ _
  obtain ⟨u, hu, -⟩ := hD.univ z₁.A _ hP' addP'
  have hE : (ev z₁.P (fst z₁.A z₁.A) (snd z₁.A z₁.A ≫ u)).IsLB := pull_isLB hL₁ _
  have Ku : ∀ (Y : Over S) (a b : Y ⟶ z₁.A), evc hP' a b = evc hL₁ a (b ≫ u) := by
    intro Y a b
    have cc : cls _ hP' = cls _ hE := (cls_eq_iff hP' hE).2 hu
    have k := evc_ev hL₁ (fst z₁.A z₁.A) (snd z₁.A z₁.A ≫ u) hE a b
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k, evc, evc, cc]
  haveI hum : IsMonHom u :=
    isMonHom_of_classifying S z₁.A z₁.A z₁.A _ z₁.P hD (additive z₁).2 hP' addP's u hu
  have adj' : ∀ (a : ord d) (Y : Over S) (x y : Y ⟶ z₁.A),
      evc hP' (x ≫ act₁ a) y = evc hP' x (y ≫ act₁ (bar d a)) := by
    intro a Y x y
    rw [K', K']
    simp only [Category.assoc, hact]
    rw [← Category.assoc x, evc_adj z₂ ha₂, Category.assoc]
  have comm : ∀ N, act₁ N ≫ u = u ≫ act₁ N := by
    intro N
    apply hD.eq_of_evc (T := z₁.A)
    have step : ∀ (Y : Over S) (x y : Y ⟶ z₁.A),
        evc hL₁ x (y ≫ act₁ N ≫ u) = evc hL₁ x (y ≫ u ≫ act₁ N) := by
      intro Y x y
      calc evc hL₁ x (y ≫ act₁ N ≫ u) = evc hP' x (y ≫ act₁ N) := by rw [Ku, Category.assoc]
        _ = evc hP' (x ≫ act₁ (bar d N)) y := by rw [adj', bar_bar hd]
        _ = evc hL₁ (x ≫ act₁ (bar d N)) (y ≫ u) := Ku _ _ _
        _ = evc hL₁ x ((y ≫ u) ≫ act₁ (bar d (bar d N))) := evc_adj z₁ ha₁ _ _ _
        _ = evc hL₁ x (y ≫ u ≫ act₁ N) := by rw [bar_bar hd, Category.assoc]
    exact step _ _ _
  haveI := hi
  haveI := hpr
  haveI := he
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : c.A ⟶ c.A, ψ = inc₁ ≫ u ≫ pr₁ := ⟨_, rfl⟩
  have hincu : inc₁ ≫ u = ψ ≫ inc₁ := by
    calc inc₁ ≫ u = (inc₁ ≫ pr₁ ≫ inc₁) ≫ u := by rw [← Category.assoc inc₁ pr₁, hip, Category.id_comp]
      _ = inc₁ ≫ act₁ (idem d) ≫ u := by rw [← hpi]; simp only [Category.assoc]
      _ = inc₁ ≫ u ≫ act₁ (idem d) := by rw [comm]
      _ = ψ ≫ inc₁ := by rw [← hpi]; simp only [hψdef, Category.assoc]
  have hγ : ∀ (z : SiegPre (8 * h) M (zetaAway M) t) (inc : c.A ⟶ z.A),
      LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (Y : Over S) (a b : Y ⟶ c.A),
      evc c.isLB a b = evc z.isLB (a ≫ inc) (b ≫ inc) := by
    intro z inc hc Y a b
    have h1 := pull_isLB z.isLB (inc ⊗ₘ inc).left
    have cc := (cls_eq_iff c.isLB h1).2 hc
    rw [evc, evc, cc, cls_pull z.isLB _ h1, ← pull_comp, ← Over.comp_left, lift_map]
  have hψ : ∀ (Y : Over S) (a b : Y ⟶ c.A), evc c.isLB a (b ≫ ψ) = evc c.isLB a b := by
    intro Y a b
    rw [hγ z₁ inc₁ hc₁ _ a (b ≫ ψ), hγ z₂ inc₂ hc₂ _ a b, Category.assoc b ψ, ← hincu, ← Category.assoc, ← Ku, K',
      ← hinc]
    simp only [Category.assoc]
  have hw : (ψ * (𝟙 c.A)⁻¹) ^ d = 1 := by
    refine hker.2 c.A _ ((triv_ev_iff c.isLB _ _).2 ?_)
    rw [evc_symm c]
    have e1 := evc_mul_right c (fst c.A c.A) (snd c.A c.A ≫ (ψ * (𝟙 c.A)⁻¹)) (snd c.A c.A)
    have e2 : (snd c.A c.A ≫ (ψ * (𝟙 c.A)⁻¹)) * snd c.A c.A = snd c.A c.A ≫ ψ := by
      conv_rhs => rw [← inv_mul_cancel_right ψ (𝟙 c.A)]
      rw [MonObj.comp_mul (snd c.A c.A) (ψ * (𝟙 c.A)⁻¹) (𝟙 c.A), Category.comp_id]
    rw [e2, hψ] at e1
    exact left_eq_add.1 (e1.trans (add_comm _ _))
  haveI : IsMonHom ψ := by rw [hψdef]; infer_instance
  have hψd : (𝟙 c.A ^ d) ≫ ψ = (𝟙 c.A ^ d) ≫ 𝟙 c.A := by
    rw [MonObj.pow_comp, Category.id_comp, Category.comp_id]
    rw [mul_pow, inv_pow, mul_inv_eq_one] at hw
    exact hw
  have hψ1 : ψ = 𝟙 c.A := cancel_pow S c.A c.A c.ab d hd ψ (𝟙 _) hψd
  have hincu' : inc₁ ≫ u = inc₁ := by rw [hincu, hψ1, Category.id_comp]
  have hsum := act_sum hr₁ Finset.univ (fun k ↦ colU d k * idem d * rowU d k)
  rw [← natCast_eq_sum, act_natCast hr₁] at hsum
  have key : (𝟙 z₁.A ^ d) ≫ u = (𝟙 z₁.A ^ d) ≫ 𝟙 _ := by
    rw [hsum, prod_comp, Category.comp_id]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [hr₁.2.2.1, hr₁.2.2.1, ← hpi]
    simp only [Category.assoc]
    rw [comm, ← Category.assoc inc₁ u, hincu']
  have hu1 : u = 𝟙 _ := cancel_pow S z₁.A z₁.A z₁.ab d hd u (𝟙 _) key
  have cc : cls _ hP' = cls z₁.P hL₁ := by
    rw [(cls_eq_iff hP' hE).2 hu, cls_pull hL₁ _ hE, hu1, Category.comp_id, lift_fst_snd, Over.id_left, pull_id]
  exact (cls_eq_iff hL₁ hP').1 cc.symm

end GlobalTheory.ZarhinUniqBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickBundleUniqueOfOrderLinearIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTrick_bundle_unique_of_order_linear_iso : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)) (inc₁ : c.A ⟶ z₁.A) (pr₁ : z₁.A ⟶ c.A) (inc₂ : c.A ⟶ z₂.A) (e : z₁.A ≅ z₂.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → IsMonHom inc₁ → IsMonHom pr₁ → inc₁ ≫ pr₁ = 𝟙 c.A → pr₁ ≫ inc₁ = act₁ (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z₁.P.pull (inc₁ ⊗ₘ inc₁).left) → LBIso c.P (z₂.P.pull (inc₂ ⊗ₘ inc₂).left) → IsMonHom e.hom → inc₁ ≫ e.hom = inc₂ → (∀ o, act₁ o ≫ e.hom = e.hom ≫ act₂ o) → LBIso z₁.P (z₂.P.pull (e.hom ⊗ₘ e.hom).left) := by
  first | (exact @GlobalTheory.ZarhinUniqBundle.lbIso_of_ordLinear) | (exact GlobalTheory.ZarhinUniqBundle.lbIso_of_ordLinear) | (intros; apply GlobalTheory.ZarhinUniqBundle.lbIso_of_ordLinear  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationUnitKernelLeKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationUnitKernelLeKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinKer

open Matrix GlobalTheory.ZarhinFam

def kerN (d : ℕ) : ord d :=
  ⟨form d * single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [Matrix.mul_apply, single]⟩

def kerM (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inr 0) 1 * formInv d, fun i j => by simp [Matrix.mul_apply, single]⟩

theorem idem_mul_kerN (d : ℕ) : idem d * kerN d = polUnit d := by
  ext1
  simp only [Subring.coe_mul, idem, kerN, polUnit_coe]
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single]
  simp [form]

theorem kerM_mul_bar_kerN {d : ℕ} (hd : 0 < d) : kerM d * bar d (kerN d) = idem d := by
  ext1
  simp only [Subring.coe_mul, bar_coe, kerM, kerN, idem, Matrix.transpose_mul, transpose_single, form_transpose]
  calc single (Sum.inl 0) (Sum.inr 0) (1 : ℤ) * formInv d *
        (form d * (single (Sum.inr 0) (Sum.inl 0) 1 * form d) * formInv d)
      = single (Sum.inl 0) (Sum.inr 0) (1 : ℤ) * (formInv d * form d) * single (Sum.inr 0) (Sum.inl 0) 1 *
          (form d * formInv d) := by simp only [Matrix.mul_assoc]
    _ = single (Sum.inl 0) (Sum.inl 0) 1 := by
      rw [formInv_mul_form hd, form_mul_formInv hd, Matrix.mul_one, Matrix.mul_one, single_mul_single_same, _root_.one_mul]

end GlobalTheory.ZarhinKer

namespace GlobalTheory.ZarhinKer

open GlobalTheory.ZarhinFam

theorem polUnit_ker_le : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 → ∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen := by
  intro h M d hd S t c z act inc pr _hdu _hker _hprin hact hadj _hinc _hpr hip hpi hP T x hx
  have hinc_idem : inc ≫ act (idem d) = inc := by
    rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hN : inc ≫ act (kerN d) = inc ≫ act (polUnit d) := by
    calc inc ≫ act (kerN d) = (inc ≫ act (idem d)) ≫ act (kerN d) := by rw [hinc_idem]
      _ = inc ≫ act (polUnit d) := by rw [Category.assoc, ← hact.2.2.1, idem_mul_kerN]
  have hM : inc ≫ act (kerM d) ≫ act (bar d (kerN d)) = inc := by
    rw [← hact.2.2.1, kerM_mul_bar_kerN hd, hinc_idem]
  have hv : (snd c.A T ≫ x ≫ inc) ≫ act (kerN d) = 1 := by
    rw [Category.assoc, Category.assoc, hN, hx, comp_one]
  have e1 : ((fst c.A T ≫ inc ≫ act (kerM d)) ≫ lift (1 : z.A ⟶ z.A) (𝟙 z.A)).left =
      (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc ≫ act (kerM d))).left ≫
        (lift (fst z.A z.A ≫ act (kerN d)) (snd z.A z.A)).left := by
    rw [← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, comp_one]
      rw [← hv]; simp only [Category.assoc]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, Category.comp_id]
  have e2 : (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc)).left =
      (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc ≫ act (kerM d))).left ≫
        (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar d (kerN d)))).left := by
    rw [← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, lift_fst, lift_fst_assoc]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, hM]
  have e3 : (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc)).left =
      (lift (snd c.A T ≫ x) (fst c.A T)).left ≫ (inc ⊗ₘ inc).left := by
    rw [← Over.comp_left]
    congr 1
    rw [lift_map, Category.assoc]
  have i1 := GlobalTheory.GenSpread.lbIso_pull_comp _ e1 e2 (hadj (kerN d))
  have i2 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP (lift (snd c.A T ≫ x) (fst c.A T)).left e3
  obtain ⟨t0, ht0⟩ := z.rig₁
  have g1 : ∃ u : LB.Gen (z.P.pull ((fst c.A T ≫ inc ≫ act (kerM d)) ≫ lift (1 : z.A ⟶ z.A) (𝟙 z.A)).left),
      u.IsGen :=
    ⟨LB.pullGen z.P _ _ t0 (fst c.A T ≫ inc ≫ act (kerM d)).left,
      LB.isGen_pullGen z.P _ _ t0 ht0 (fst c.A T ≫ inc ≫ act (kerM d)).left⟩
  have g2 := GlobalTheory.RigidBundleGlue.exists_gen_of_lbIso (pull_isLB z.isLB _) (pull_isLB z.isLB _) i1 g1
  exact GlobalTheory.RigidBundleGlue.exists_gen_of_lbIso (pull_isLB z.isLB _) (pull_isLB c.isLB _) i2.symm g2

end GlobalTheory.ZarhinKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationUnitKernelLeKernelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 → ∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen := by
  first | (exact @GlobalTheory.ZarhinKer.polUnit_ker_le) | (exact GlobalTheory.ZarhinKer.polUnit_ker_le) | (intros; apply GlobalTheory.ZarhinKer.polUnit_ker_le  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationKernelLeUnitKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationKernelLeUnitKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

open Matrix

def formPolUnit (d : ℕ) : ord d :=
  ⟨form d * single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [Matrix.mul_apply, Matrix.single_apply]⟩

theorem idem_mul_formPolUnit (d : ℕ) : idem d * formPolUnit d = polUnit d := by
  ext1
  show single (Sum.inl 0) (Sum.inl 0) 1 * (form d * single (Sum.inl 0) (Sum.inr 0) 1) = single (Sum.inl 0) (Sum.inr 0) 1
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single]
  simp [form]

theorem bar_formPolUnit_mul_idem {d : ℕ} (hd : 0 < d) : bar d (formPolUnit d) * idem d = bar d (formPolUnit d) := by
  ext1
  have e : ((bar d (formPolUnit d) : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      form d * single (Sum.inr 0) (Sum.inl 0) 1 := by
    rw [bar_coe]
    show form d * (form d * single (Sum.inl 0) (Sum.inr 0) 1)ᵀ * formInv d = _
    rw [Matrix.transpose_mul, form_transpose, Matrix.transpose_single, Matrix.mul_assoc, Matrix.mul_assoc,
      form_mul_formInv hd, Matrix.mul_one]
  rw [Subring.coe_mul, e]
  show form d * single (Sum.inr 0) (Sum.inl 0) 1 * single (Sum.inl 0) (Sum.inl 0) 1 = _
  rw [Matrix.mul_assoc, Matrix.single_mul_single_same, _root_.mul_one]

end GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinFam.KerSup

variable {X Y : Scheme.{0}}

theorem exists_gen_of_lbIso' {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullId P) (chartPullPull Q (𝟙 X)) h
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X)) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem gen_pull_comp (L : LB X) (f : Y ⟶ X) {Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (H : ∃ t : LB.Gen (L.pull f), t.IsGen) : ∃ t : LB.Gen (L.pull (h ≫ f)), t.IsGen := by
  obtain ⟨t, ht⟩ := H
  exact gen_chartPull (chartPullSame L (fun _ => h ≫ f) (fun _ => f) (fun _ => 1) h (fun _ => rfl)) t ht

theorem gen_congr (L : LB X) {f g : Y ⟶ X} (e : f = g)
    (H : ∃ t : LB.Gen (L.pull f), t.IsGen) : ∃ t : LB.Gen (L.pull g), t.IsGen := by
  subst e; exact H

theorem lbIso_pull_comp (L : LB X) {f g : Y ⟶ X} {Y' : Scheme.{0}} (h : Y' ⟶ Y) (H : LBIso (L.pull f) (L.pull g)) :
    LBIso (L.pull (h ≫ f)) (L.pull (h ≫ g)) :=
  H.chartPull (chartPullSame L (fun _ => h ≫ f) (fun _ => f) (fun _ => 1) h (fun _ => rfl))
    (chartPullSame L (fun _ => h ≫ g) (fun _ => g) (fun _ => 1) h (fun _ => rfl))

theorem lbIso_pull_pull {L : LB X} {M : LB Y} {j : X ⟶ Y} {Y' : Scheme.{0}} (h : Y' ⟶ X) (H : LBIso L (M.pull j)) :
    LBIso (L.pull h) (M.pull (h ≫ j)) := by
  have a : ChartPull (L.pull h) L h := chartPullPull L h
  have b : ChartPull (M.pull (h ≫ j)) (M.pull j) h :=
    chartPullSame M (fun _ => h ≫ j) (fun _ => j) (fun _ => 1) h (fun _ => rfl)
  exact LBIso.chartPull a b H

end GlobalTheory.ZarhinFam.KerSup

namespace GlobalTheory.ZarhinFam

theorem ker_pol_le_ker_polUnit : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), (∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen) → x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 := by
  intro h M d hd S t c z act inc pr hdu hker hz hact hadj hinc hpr hip hpi hP T x hx
  have hNp : act (polUnit d) = act (idem d) ≫ act (formPolUnit d) := by
    rw [← idem_mul_formPolUnit, hact.2.2.1]
  have hbar : act (bar d (formPolUnit d)) ≫ pr ≫ inc = act (bar d (formPolUnit d)) := by
    rw [hpi, ← hact.2.2.1, bar_formPolUnit_mul_idem hd]
  have hy : x ≫ inc ≫ act (polUnit d) = x ≫ inc ≫ act (formPolUnit d) := by
    rw [hNp, ← hpi]
    simp only [Category.assoc]
    rw [← Category.assoc inc pr, hip, Category.id_comp]
  rw [hy]
  apply hz.2 T
  let q : z.A ⟶ c.A := act (bar d (formPolUnit d)) ≫ pr
  let ψ₁ : z.A ⊗ T ⟶ c.A ⊗ c.A := lift (snd z.A T ≫ x) (fst z.A T ≫ q)
  let φ : z.A ⊗ T ⟶ z.A ⊗ z.A := lift (snd z.A T ≫ x ≫ inc) (fst z.A T)
  have g1 : ∃ u : (c.P.pull ψ₁.left).Gen, u.IsGen := by
    have := KerSup.gen_pull_comp c.P _ (lift (fst z.A T ≫ q) (snd z.A T)).left hx
    refine KerSup.gen_congr c.P ?_ this
    rw [← Over.comp_left]
    congr 1
    simp [ψ₁]
  have g2 : ∃ u : (z.P.pull (ψ₁.left ≫ (inc ⊗ₘ inc).left)).Gen, u.IsGen :=
    KerSup.exists_gen_of_lbIso' (pull_isLB c.isLB _) (pull_isLB z.isLB _) (KerSup.lbIso_pull_pull ψ₁.left hP) g1
  have e3 : ψ₁.left ≫ (inc ⊗ₘ inc).left =
      φ.left ≫ (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar d (formPolUnit d)))).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [ψ₁, φ, q, lift_map, comp_lift, lift_fst, lift_snd_assoc, Category.assoc, hbar]
  have i4 := KerSup.lbIso_pull_comp z.P φ.left (hadj (formPolUnit d))
  have g4 := KerSup.exists_gen_of_lbIso' (pull_isLB z.isLB _) (pull_isLB z.isLB _) i4.symm
    (KerSup.gen_congr z.P e3 g2)
  refine KerSup.gen_congr z.P ?_ g4
  rw [← Over.comp_left]
  congr 1
  simp [φ]

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationKernelLeUnitKernelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), (∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen) → x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit) | (exact GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit) | (intros; apply GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickPrincipalObjectsIsoUnique
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem actPB_of_zRel : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∀ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₁ act₁ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  intro h M d _ _ _ hd _ jl n o κ S t c z₁ z₂ act₁ act₂ hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂ hZ₁ hZ₂
  obtain ⟨inc₁, pr₁, hi₁, hp₁, hip₁, hpi₁, hL₁, -, hz₁⟩ := hZ₁
  obtain ⟨inc₂, pr₂, hi₂, hp₂, hip₂, hpi₂, hL₂, -, hz₂⟩ := hZ₂
  have hker : ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔
      x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1 := fun T x =>
    ⟨fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x hx),
     fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x hx)⟩
  obtain ⟨e, he, hinc, hact⟩ := GlobalTheory.T.zarhinTrick_actions_isomorphic h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ pr₂ hdS hA₁ hA₂
    hi₁ hp₁ hip₁ hpi₁ hi₂ hp₂ hip₂ hpi₂ hker
  have hLB := GlobalTheory.T.zarhinTrick_bundle_unique_of_order_linear_iso h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ e hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂
    hi₁ hp₁ hip₁ hpi₁ hL₁ hL₂ he hinc hact
  haveI := he
  refine ⟨e.hom.left, (e.hom ⊗ₘ e.hom).left, isGrpPullback_of_iso e, ⟨?_, ?_⟩, hLB, fun a => ?_, fun o => ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  · rw [Category.id_comp, ← Over.comp_left, hz₁ a, hz₂ a]
    congr 1
    have key := map_list_prod (IsMonHom.monoidHom e.hom (𝟙_ (Over S)))
      (List.ofFn fun k => c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))
    refine key.trans ?_
    rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    show (c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)) ≫ e.hom = _
    rw [Category.assoc, Category.assoc, hact, ← Category.assoc inc₁, hinc]
  · rw [← Over.comp_left, ← Over.comp_left, hact o]

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickPrincipalObjectsIsoUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTrick_principal_objects_iso_unique : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∀ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₁ act₁ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  first | (exact @GlobalTheory.ZarhinFam.actPB_of_zRel) | (exact GlobalTheory.ZarhinFam.actPB_of_zRel) | (intros; apply GlobalTheory.ZarhinFam.actPB_of_zRel  <;> assumption)
end
