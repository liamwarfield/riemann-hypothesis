module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifference
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMorphismOfGeneratingSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.LevAlg

variable {S : Scheme.{0}}

section Hom

variable {G H : Over S} [GrpObj G] [GrpObj H]

theorem isMonHom_of_mulComp (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  · simpa only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd] using
      h (G ⊗ G) (fst G G) (snd G G)

theorem isMonHom_mul [IsCommMonObj H] (f g : G ⟶ H) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) :=
  isMonHom_of_mulComp _ fun T x y ↦ by
    simp only [MonObj.comp_mul, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _

theorem isMonHom_one : IsMonHom (1 : G ⟶ H) :=
  isMonHom_of_mulComp _ fun T x y ↦ by simp

theorem isMonHom_zpow [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f] (n : ℤ) : IsMonHom (f ^ n) :=
  isMonHom_of_mulComp _ fun T x y ↦ by
    simp only [GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]

theorem isMonHom_prod [IsCommMonObj H] {K : Type} (s : Finset K) (f : K → (G ⟶ H))
    (hf : ∀ i, IsMonHom (f i)) : IsMonHom (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isMonHom_one : IsMonHom (1 : G ⟶ H))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    haveI := hf a
    exact isMonHom_mul _ _

end Hom

section Obj

variable (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  unfold mkZ pa
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  unfold mkZ pb
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem zob_ext {T : Over S} (f g : T ⟶ Zob A B) (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance isMonHom_pa (i : Fin 4) : IsMonHom (pa A B i) := by
  unfold pa; infer_instance

instance isMonHom_pb (j : Fin 4) : IsMonHom (pb A B j) := by
  unfold pb; infer_instance

theorem isMonHom_mkZ {T : Over S} [GrpObj T] (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B))
    (hu : ∀ i, IsMonHom (u i)) (hv : ∀ j, IsMonHom (v j)) : IsMonHom (mkZ A B u v) :=
  isMonHom_of_mulComp _ fun T' x y ↦ by
    apply zob_ext
    · intro i
      haveI := hu i
      simp only [Category.assoc, mkZ_pa, MonObj.mul_comp]
    · intro j
      haveI := hv j
      simp only [Category.assoc, mkZ_pb, MonObj.mul_comp]

theorem isMonHom_incZ : IsMonHom (incZ A B) := by
  unfold incZ
  apply isMonHom_mkZ
  · intro i
    split_ifs
    · infer_instance
    · exact isMonHom_one
  · intro j
    exact isMonHom_one

theorem isMonHom_actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) [IsMonHom la] [IsMonHom mu] (N : ord d) :
    IsMonHom (actZ A B d la mu N) := by
  unfold actZ
  apply isMonHom_mkZ
  · intro i
    apply isMonHom_prod
    intro j
    haveI := isMonHom_zpow (pa A B j) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inl i))
    haveI := isMonHom_zpow (pb A B j ≫ mu)
      ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inl i) / (d : ℤ))
    exact isMonHom_mul _ _
  · intro i
    apply isMonHom_prod
    intro j
    haveI := isMonHom_zpow (pa A B j ≫ la) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inr i))
    haveI := isMonHom_zpow (pb A B j) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inr i))
    exact isMonHom_mul _ _

end Obj

end GlobalTheory.ZarhinFam.LevAlg

namespace GlobalTheory.ZarhinFam.LevAlg

theorem levZ_add_tors : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a b, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (a + b) = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a * (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) ∧ ∀ a, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a ^ M = 1 := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _ κ _
  haveI : IsMonHom la := hZ.2.2.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  have hg : ∀ k, IsMonHom (incZ c.A B ≫ actZ c.A B d la mu (oMat d k)) := fun k => by
    haveI := isMonHom_incZ c.A B
    haveI := isMonHom_actZ c.A B d la mu (oMat d k)
    infer_instance
  constructor
  · intro a b
    simp only [levZ, List.prod_ofFn]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    haveI := hg k
    rw [map_add (f := _), c.lev_add, MonObj.mul_comp]
  · intro a
    simp only [levZ, List.prod_ofFn]
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun k _ => ?_
    haveI := hg k
    rw [← MonObj.pow_comp, c.lev_tors]
    simp

end GlobalTheory.ZarhinFam.LevAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinLevel_additive_killed_by_level : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a b, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (a + b) = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a * (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) ∧ ∀ a, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a ^ M = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (exact GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (intros; apply GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClauses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClauses
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.RelAlg

open GlobalTheory.ZarhinFam

section Obj

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa]
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb]
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem zob_ext {T : Over S} {f g : T ⟶ Zob A B} (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance isMonHom_pa (i : Fin 4) : IsMonHom (pa A B i) := by
  unfold pa
  infer_instance

instance isMonHom_pb (j : Fin 4) : IsMonHom (pb A B j) := by
  unfold pb
  infer_instance

theorem isMonHom_of_coords {X : Over S} [MonObj X] (f : X ⟶ Zob A B)
    (ha : ∀ i, IsMonHom (f ≫ pa A B i)) (hb : ∀ j, IsMonHom (f ≫ pb A B j)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · apply zob_ext A B
    · intro i
      have := ha i
      simp only [Category.assoc, IsMonHom.one_hom (f := f ≫ pa A B i),
        IsMonHom.one_hom (f := pa A B i)]
    · intro j
      have := hb j
      simp only [Category.assoc, IsMonHom.one_hom (f := f ≫ pb A B j),
        IsMonHom.one_hom (f := pb A B j)]
  · apply zob_ext A B
    · intro i
      have := ha i
      simp only [Category.assoc, IsMonHom.mul_hom (f := f ≫ pa A B i),
        IsMonHom.mul_hom (f := pa A B i), MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    · intro j
      have := hb j
      simp only [Category.assoc, IsMonHom.mul_hom (f := f ≫ pb A B j),
        IsMonHom.mul_hom (f := pb A B j), MonoidalCategory.tensorHom_comp_tensorHom_assoc]

theorem isMonHom_incZ : IsMonHom (incZ A B) := by
  apply isMonHom_of_coords
  · intro i
    rw [incZ, mkZ_pa]
    split_ifs
    · infer_instance
    · exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  · intro j
    rw [incZ, mkZ_pb]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[B]))

theorem isMonHom_prZ : IsMonHom (prZ A B) := by
  unfold prZ pa
  infer_instance

theorem incZ_prZ : incZ A B ≫ prZ A B = 𝟙 A := by
  rw [incZ, prZ, mkZ_pa]
  simp

theorem prZ_incZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) : prZ A B ≫ incZ A B = actZ A B d la mu (idem d) := by
  apply zob_ext
  · intro i
    rw [Category.assoc, incZ, mkZ_pa, actZ, mkZ_pa]
    fin_cases i <;> simp [prZ, idem, Matrix.single_apply, Fin.prod_univ_four, MonObj.comp_one]
  · intro j
    rw [Category.assoc, incZ, mkZ_pb, actZ, mkZ_pb]
    fin_cases j <;> simp [prZ, idem, Matrix.single_apply, Fin.prod_univ_four, MonObj.comp_one]

end Obj

end GlobalTheory.ZarhinFam.RelAlg

noncomputable section

namespace GlobalTheory.ZarhinFam.RelAlg

open GlobalTheory.ZarhinFam

section Lev

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def precompHom {X Y M : Over S} [GrpObj M] [IsCommMonObj M] (x : X ⟶ Y) : (Y ⟶ M) →* (X ⟶ M) where
  toFun g := x ≫ g
  map_one' := MonObj.comp_one x
  map_mul' g₁ g₂ := MonObj.comp_mul x g₁ g₂

theorem one_comp_actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) [IsMonHom la] [IsMonHom mu] (N : ord d) :
    (1 : 𝟙_ (Over S) ⟶ Zob A B) ≫ actZ A B d la mu N = 1 := by
  apply zob_ext
  · intro i
    rw [Category.assoc, actZ, mkZ_pa, MonObj.one_comp (pa A B i)]
    change precompHom (1 : 𝟙_ (Over S) ⟶ Zob A B) _ = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [map_mul, map_zpow, map_zpow]
    change (1 ≫ pa A B j) ^ _ * (1 ≫ pb A B j ≫ mu) ^ _ = 1
    rw [MonObj.one_comp, ← Category.assoc, MonObj.one_comp, MonObj.one_comp]
    simp
  · intro j
    rw [Category.assoc, actZ, mkZ_pb, MonObj.one_comp (pb A B j)]
    change precompHom (1 : 𝟙_ (Over S) ⟶ Zob A B) _ = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_mul, map_zpow, map_zpow]
    change (1 ≫ pa A B k ≫ la) ^ _ * (1 ≫ pb A B k) ^ _ = 1
    rw [MonObj.one_comp (pa A B k ≫ la), MonObj.one_comp (pb A B k)]
    simp

theorem oMat_zero (d : ℕ) : oMat d 0 = idem d := rfl

end Lev

end GlobalTheory.ZarhinFam.RelAlg

namespace GlobalTheory.ZarhinFam

open GlobalTheory.ZarhinFam.RelAlg

theorem zRel_alg : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → IsMonHom (GlobalTheory.ZarhinFam.incZ c.A B) ∧ IsMonHom (GlobalTheory.ZarhinFam.prZ c.A B) ∧ GlobalTheory.ZarhinFam.incZ c.A B ≫ GlobalTheory.ZarhinFam.prZ c.A B = 𝟙 c.A ∧ GlobalTheory.ZarhinFam.prZ c.A B ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.idem d) ∧ ∀ a, c.lev a ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (GlobalTheory.ZarhinFam.jlMap h a) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _ κ hκ
  haveI : IsMonHom la := hZ.2.2.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  haveI := isMonHom_incZ c.A B
  have hpi := prZ_incZ c.A B d la mu
  refine ⟨isMonHom_incZ c.A B, isMonHom_prZ c.A B, incZ_prZ c.A B, hpi, fun a => ?_⟩
  have hlev0 : c.lev 0 = 1 := by
    have h0 := c.lev_add 0 0
    rw [add_zero] at h0
    exact left_eq_mul.mp h0
  rw [levZ, List.prod_ofFn, Fintype.prod_eq_single 0 (fun k hk => by
    rw [hκ.2.2 k hk a, hlev0, ← Category.assoc, MonObj.one_comp, one_comp_actZ])]
  rw [hκ.2.1 a, oMat_zero, ← hpi, ← Category.assoc (incZ c.A B), incZ_prZ, Category.id_comp]

end GlobalTheory.ZarhinFam
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClausesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinProduct_relation_algebraic_clauses : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → IsMonHom (GlobalTheory.ZarhinFam.incZ c.A B) ∧ IsMonHom (GlobalTheory.ZarhinFam.prZ c.A B) ∧ GlobalTheory.ZarhinFam.incZ c.A B ≫ GlobalTheory.ZarhinFam.prZ c.A B = 𝟙 c.A ∧ GlobalTheory.ZarhinFam.prZ c.A B ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.idem d) ∧ ∀ a, c.lev a ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (GlobalTheory.ZarhinFam.jlMap h a) := by
  first | (exact @GlobalTheory.ZarhinFam.zRel_alg) | (exact GlobalTheory.ZarhinFam.zRel_alg) | (intros; apply GlobalTheory.ZarhinFam.zRel_alg  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocal

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem pullU_comp' {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (f ≫ g) U x = pullU f (g ⁻¹ᵁ U) (pullU g U x) := by
  apply Units.ext
  simp only [pullU, Scheme.Hom.comp_app, Units.coe_map]
  rfl

theorem gen_pull3 {X Y Z Z' Y' : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (h : Z' ⟶ Z)
    (c : Y' ⟶ X) (e : Z' ⟶ Y') (heq : h ≫ b ≫ a = e ≫ c)
    (hg : ∃ t : LB.Gen ((L.pull a).pull b), t.IsGen) : ∃ t : LB.Gen ((L.pull c).pull e), t.IsGen := by
  obtain ⟨t, ht⟩ := hg
  have h1 : ∃ t : LB.Gen (((L.pull a).pull b).pull h), t.IsGen :=
    ⟨LB.genPull _ t h, LB.isGen_genPull _ t ht h⟩
  have hb : ∀ z : Z', a.base (b.base (h.base z)) = c.base (e.base z) := fun z => by
    have := congrArg (fun φ => φ.base z) heq
    simpa using this
  have hmem : ∀ (j : PUnit.{1} → PUnit.{1} → L.ι) (z : Z'), z ∈ ((L.pull c).pull e).U j →
      z ∈ (((L.pull a).pull b).pull h).U (fun _ => j) := by
    intro j z hz
    have h1 := (mem_wchart_pu L c _ _).1 ((mem_wchart_pu (L.pull c) e j z).1 hz)
    apply (mem_wchart_pu ((L.pull a).pull b) h _ z).2
    apply (mem_wchart_pu (L.pull a) b j _).2
    apply (mem_wchart_pu L a _ _).2
    rw [hb z]
    exact h1
  refine exists_gen_transfer (L := ((L.pull a).pull b).pull h) (L' := (L.pull c).pull e)
    (fun j => fun _ => j) (fun j z hz => hmem j z hz) ?_ h1
  intro i j y hy
  have hy1 : y ∈ (e ≫ c) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) :=
    pull_inf_le L c _ _ (pull_inf_le (L.pull c) e i j hy)
  have hy2 : y ∈ (h ≫ b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) := by
    rw [heq]; exact hy1
  have hm : y ∈ h ⁻¹ᵁ (((L.pull a).pull b).U i ⊓ ((L.pull a).pull b).U j) :=
    pull_inf_le ((L.pull a).pull b) h (fun _ => i) (fun _ => j) ⟨hmem i y hy.1, hmem j y hy.2⟩
  have hy' : h.base y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) := hy2
  refine (germ_pull_pull L c e i j y hy hy1).trans ((gU_pullU_congr heq.symm _ _ y hy1 hy2).trans ?_)
  refine Eq.trans ?_ (germ_pull ((L.pull a).pull b) h (fun _ => i) (fun _ => j) y _ hm).symm
  have hy3 : y ∈ h ⁻¹ᵁ ((b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit))) := hy2
  rw [gU_pullU h _ y hm, germ_pull_pull L a b i j (h.base y) hm hy', ← gU_pullU h _ y hy3]
  erw [pullU_comp']
  rfl

end GlobalTheory.KerKilledLocal

namespace GlobalTheory.KerKilledLocal

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

noncomputable section Grp

variable {S' : Scheme.{0}} (G : Over S') [GrpObj G] [IsCommMonObj G]

theorem lift_left_fst' {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) :
    (lift a b).left ≫ (fst X Y).left = a.left := by
  rw [← Over.comp_left, lift_fst]

theorem lift_left_snd' {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) :
    (lift a b).left ≫ (snd X Y).left = b.left := by
  rw [← Over.comp_left, lift_snd]

theorem lift_left_fst'_assoc {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) {Q : Scheme.{0}}
    (q : X.left ⟶ Q) : (lift a b).left ≫ (fst X Y).left ≫ q = a.left ≫ q := by
  rw [← Category.assoc, lift_left_fst']

theorem lift_left_snd'_assoc {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) {Q : Scheme.{0}}
    (q : Y.left ⟶ Q) : (lift a b).left ≫ (snd X Y).left ≫ q = b.left ≫ q := by
  rw [← Category.assoc, lift_left_snd']

def down (V : S'.Opens) {T : Over V.toScheme} (x : T ⟶ (Over.pullback V.ι).obj G) :
    Over.mk (T.hom ≫ V.ι) ⟶ G :=
  Over.homMk (x.left ≫ pullback.fst G.hom V.ι) (by
    have wx : x.left ≫ pullback.snd G.hom V.ι = T.hom := Over.w x
    change (x.left ≫ pullback.fst G.hom V.ι) ≫ G.hom = T.hom ≫ V.ι
    rw [Category.assoc, pullback.condition, ← Category.assoc, wx])

theorem down_mul (V : S'.Opens) {T : Over V.toScheme} (x y : T ⟶ (Over.pullback V.ι).obj G) :
    down G V (x * y) = down G V x * down G V y := by
  apply Over.OverMorphism.ext
  exact ((isGrpPullback V.ι G).2 T x y (down G V x) (down G V y) rfl rfl).symm

theorem down_injective (V : S'.Opens) {T : Over V.toScheme} (x y : T ⟶ (Over.pullback V.ι).obj G)
    (h : down G V x = down G V y) : x = y := by
  have h1 : x.left ≫ pullback.fst G.hom V.ι = y.left ≫ pullback.fst G.hom V.ι :=
    congrArg CommaMorphism.left h
  have wx : x.left ≫ pullback.snd G.hom V.ι = T.hom := Over.w x
  have wy : y.left ≫ pullback.snd G.hom V.ι = T.hom := Over.w y
  exact Over.OverMorphism.ext (pullback.hom_ext h1 (wx.trans wy.symm))

theorem down_one (V : S'.Opens) {T : Over V.toScheme} :
    down G V (1 : T ⟶ (Over.pullback V.ι).obj G) = 1 := by
  have h := down_mul G V (1 : T ⟶ (Over.pullback V.ι).obj G) 1
  rw [_root_.mul_one] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem down_pow (V : S'.Opens) {T : Over V.toScheme} (x : T ⟶ (Over.pullback V.ι).obj G) (n : ℕ) :
    down G V (x ^ n) = down G V x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, down_one]
  | succ n ih => rw [pow_succ, pow_succ, down_mul, ih]

theorem comp_pow_pt {A B : Over S'} (f : A ⟶ B) (g : B ⟶ G) (n : ℕ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end Grp

end GlobalTheory.KerKilledLocal

namespace GlobalTheory.KerKilledLocal

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison GlobalTheory.KerKilledLocus

noncomputable section Main

variable {S' : Scheme.{0}} (G : Over S') [GrpObj G] [IsCommMonObj G]

theorem step (d : ℕ) (P : LB (G2 G).left) (V W : S'.Opens) (hV : KerKilledOn d G P V)
    (T : Over W.toScheme) (x : T ⟶ (Over.pullback W.ι).obj G)
    (hs : ∃ s : ((P.pull (pφ₂ W.ι G)).pull
        (lift (snd ((Over.pullback W.ι).obj G) T ≫ x) (fst ((Over.pullback W.ι).obj G) T)).left).Gen,
        s.IsGen) :
    ((T.hom ≫ W.ι) ⁻¹ᵁ V).ι ≫ (down G W x ^ d).left =
      ((T.hom ≫ W.ι) ⁻¹ᵁ V).ι ≫ (1 : Over.mk (T.hom ≫ W.ι) ⟶ G).left := by
  set U : T.left.Opens := (T.hom ≫ W.ι) ⁻¹ᵁ V with hU
  have hr : Set.range (U.ι ≫ T.hom ≫ W.ι) ⊆ Set.range V.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact u.2
  set k := IsOpenImmersion.lift V.ι (U.ι ≫ T.hom ≫ W.ι) hr with hkdef
  have hk : k ≫ V.ι = U.ι ≫ T.hom ≫ W.ι := IsOpenImmersion.lift_fac _ _ _
  let Tp : Over V.toScheme := Over.mk k
  have wx : x.left ≫ pullback.snd G.hom W.ι = T.hom := Over.w x
  let xp : Tp ⟶ (Over.pullback V.ι).obj G :=
    Over.homMk (pullback.lift (U.ι ≫ x.left ≫ pullback.fst G.hom W.ι) k (by
      rw [hk, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc x.left, wx]))
      (pullback.lift_snd _ _ _)
  let ρ : Over.mk (Tp.hom ≫ V.ι) ⟶ Over.mk (T.hom ≫ W.ι) := Over.homMk U.ι hk.symm
  have hρ : ρ ≫ down G W x = down G V xp := by
    apply Over.OverMorphism.ext
    change U.ι ≫ x.left ≫ pullback.fst G.hom W.ι = pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι
    rw [pullback.lift_fst]

  let GW := (Over.pullback W.ι).obj G
  let GV := (Over.pullback V.ι).obj G
  let bz : (GV ⊗ Tp).left ⟶ T.left := (snd GV Tp).left ≫ U.ι
  let Z' : Over W.toScheme := Over.mk (bz ≫ T.hom)
  let v : Z' ⟶ T := Over.homMk bz rfl
  have e1 : (fst GV Tp).left ≫ pullback.snd G.hom V.ι = (GV ⊗ Tp).hom := Over.w (fst GV Tp)
  have e2 : (snd GV Tp).left ≫ k = (GV ⊗ Tp).hom := Over.w (snd GV Tp)
  let u : Z' ⟶ GW :=
    Over.homMk (pullback.lift ((fst GV Tp).left ≫ pullback.fst G.hom V.ι) (bz ≫ T.hom) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, e1, ← e2, Category.assoc, hk]
      simp only [bz, Category.assoc]))
      (pullback.lift_snd _ _ _)
  have heq : (lift u v).left ≫ (lift (snd GW T ≫ x) (fst GW T)).left ≫ pφ₂ W.ι G =
      (lift (snd GV Tp ≫ xp) (fst GV Tp)).left ≫ pφ₂ V.ι G := by
    apply adelic_GL2_ext_of_local_components G
    · simp only [Category.assoc, pφ₂_fst]
      rw [lift_left_fst'_assoc, lift_left_fst'_assoc]
      simp only [Over.comp_left, Category.assoc]
      rw [lift_left_snd'_assoc]
      change bz ≫ x.left ≫ pullback.fst G.hom W.ι = (snd GV Tp).left ≫ pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι
      rw [pullback.lift_fst]
      simp only [bz, Category.assoc]
    · simp only [Category.assoc, pφ₂_snd]
      rw [lift_left_snd'_assoc, lift_left_snd'_assoc, lift_left_fst'_assoc]
      change pullback.lift _ _ _ ≫ pullback.fst G.hom W.ι = _
      rw [pullback.lift_fst]
      rfl
  have hgen := GlobalTheory.KerKilledLocal.gen_pull3 P (pφ₂ W.ι G) _ (lift u v).left (pφ₂ V.ι G) _ heq hs
  have hxp : xp ^ d = 1 := hV Tp xp hgen
  have key : ρ ≫ down G W x ^ d = ρ ≫ 1 := by
    rw [comp_pow_pt, hρ, ← down_pow, hxp, down_one, MonObj.comp_one]
  exact congrArg CommaMorphism.left key

end Main

end GlobalTheory.KerKilledLocal

namespace GlobalTheory.KerKilledLocal

open GlobalTheory.KerKilledLocus

theorem kerKilledOn_of_local : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G]
    (P : LB (G2 G).left) (W : S'.Opens),
    (∀ p ∈ W, ∃ V : S'.Opens, p ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V) →
      GlobalTheory.KerKilledLocus.KerKilledOn d G P W := by
  intro d S' G _ _ P W hloc T x hs
  apply down_injective G W
  rw [down_pow, down_one]
  have hmem : ∀ t : T.left, (T.hom ≫ W.ι) t ∈ W := fun t => by
    have h : (T.hom ≫ W.ι) t ∈ Set.range W.ι := ⟨T.hom t, by simp⟩
    rwa [Scheme.Opens.range_ι] at h
  choose V hpV hV using fun t : T.left => hloc _ (hmem t)
  let U : T.left → T.left.Opens := fun t => (T.hom ≫ W.ι) ⁻¹ᵁ V t
  have hc : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun t _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hpV t⟩
  refine Over.OverMorphism.ext ((T.left.openCoverOfIsOpenCover U hc).hom_ext _ _ fun t => ?_)
  exact step G d P (V t) W (hV t) T x hs

end GlobalTheory.KerKilledLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelKilledOverOpen_of_local : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (W : S'.Opens), (∀ p ∈ W, ∃ V : S'.Opens, p ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V) → GlobalTheory.KerKilledLocus.KerKilledOn d G P W := by
  first | (exact @GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (exact GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (intros; apply GlobalTheory.KerKilledLocal.kerKilledOn_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegree
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem finrank_ratF_eq_gdeg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  intro hA k _ X _ p D hX P hamp e x hg
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  obtain ⟨hI, π, hπ, hgen, hr0, hr, hiso⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hamp e x hg
  obtain ⟨B, -, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hg
  obtain ⟨u, hu, -⟩ := hB 1 le_rfl
  have h1 := (hiso u hu).gdeg_eq D
  obtain ⟨hPV, hdeg, hcard⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D
  have h2 := (GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow hA k (PSpace k D) (PSpace.str k D) D hPV).1 X p hX π hπ hgen hr0 (ProjSpace.hermitianTwistingSheaf k D)
  have h3 : gdeg ((up P.L u).pow e) D = (e : ℝ) ^ D * gdeg (up P.L u) D :=
    GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow k X p D hX (up P.L u) e fun _ _ => 1
  have h4 := GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L u
  rw [← hr]
  push_cast
  rw [← hcard, ← hdeg, ← h2, ← h1, h3, h4]

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegreeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  first | exact @GlobalTheory.HSAmp.finrank_ratF_eq_gdeg | exact GlobalTheory.HSAmp.finrank_ratF_eq_gdeg | (intros; apply GlobalTheory.HSAmp.finrank_ratF_eq_gdeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemePullbackAdjointEndomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemePullbackAdjointEndomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

open GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.EndLoc.AdjClosed

variable {S : Scheme.{0}}

theorem hom_ext_sq {A : Over S} {X : Scheme.{0}} {u v : X ⟶ (A ⊗ A).left}
    (h₁ : u ≫ (fst A A).left = v ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = v ≫ (snd A A).left) : u = v := by
  have p : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  exact p.hom_ext h₁ h₂

theorem comm_left {S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hsq : IsSquare φ φ₂) (f : A ⟶ A) (g : A' ⟶ A')
    (hg : g.left ≫ φ = φ ≫ f.left) :
    (lift (fst A' A' ≫ g) (snd A' A')).left ≫ φ₂ = φ₂ ≫ (lift (fst A A ≫ f) (snd A A)).left := by
  apply hom_ext_sq
  · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
      lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hg]
    simp only [← Category.assoc, hsq.1]
  · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
      lift_snd, hsq.2]

theorem comm_right {S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hsq : IsSquare φ φ₂) (f : A ⟶ A) (g : A' ⟶ A')
    (hg : g.left ≫ φ = φ ≫ f.left) :
    (lift (fst A' A') (snd A' A' ≫ g)).left ≫ φ₂ = φ₂ ≫ (lift (fst A A) (snd A A ≫ f)).left := by
  apply hom_ext_sq
  · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
      lift_fst, hsq.1]
  · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
      lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hg]
    simp only [← Category.assoc, hsq.2]

end GlobalTheory.EndLoc.AdjClosed


open GlobalTheory.EndLoc.AdjClosed in
theorem GlobalTheory.EndLoc.exists_closed_adj : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (f f' : A ⟶ A), IsMonHom f → IsMonHom f' → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (g g' : A' ⟶ A'), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → g.left ≫ φ' = φ' ≫ f.left → g'.left ≫ φ' = φ' ≫ f'.left → (LBIso ((Q.pull φ₂').pull (lift (fst A' A' ≫ g) (snd A' A')).left) ((Q.pull φ₂').pull (lift (fst A' A') (snd A' A' ≫ g')).left) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A _ _ Q hA hQ h0l h0r hsym hamp f f' hf hf'
  let β := (lift (fst A A ≫ f) (snd A A)).left
  let β' := (lift (fst A A) (snd A A ≫ f')).left
  let N := LB.LinComb Q (K := Fin 2) ![β, β'] ![1, -1]
  have hN : N.IsLB := LB.isLB_linComb hQ _ _
  have hc : cls N hN = pull β (cls Q hQ) - pull β' (cls Q hQ) := by
    rw [cls_linComb hQ]
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  have hrig : Out.Rigidified (A ⊗ A) N := by
    have e : η[A ⊗ A] ≫ lift (fst A A ≫ f) (snd A A) = η[A ⊗ A] ≫ lift (fst A A) (snd A A ≫ f') := by
      have h₁ : η[A ⊗ A] ≫ fst A A = η[A] := IsMonHom.one_hom (fst A A)
      have h₂ : η[A ⊗ A] ≫ snd A A = η[A] := IsMonHom.one_hom (snd A A)
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.assoc, lift_fst, ← Category.assoc, h₁, IsMonHom.one_hom]
      · rw [Category.assoc, lift_snd, Category.assoc, lift_snd, ← Category.assoc, h₂, IsMonHom.one_hom]
    have e' : eSec (A ⊗ A) ≫ β = eSec (A ⊗ A) ≫ β' := by
      simp only [eSec, β, β', ← Over.comp_left, e]
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
    rw [cls_pull hN, hc, map_sub, ← pull_comp, ← pull_comp, e', sub_self]
  let L₀ := Out.boxLB (Q.pull (lift (𝟙 A) (𝟙 A)).left) (GlobalTheory.SquarePol.sqIsPowGrp A).pr
  have hL₀ : L₀.IsLB := LB.isLB_linComb (pull_isLB hQ _) _ _
  have hamp₀ : Out.RelAmple (A ⊗ A) L₀ :=
    GlobalTheory.relAmple_boxLB S _ A 2 (GlobalTheory.SquarePol.sqIsPowGrp A) _ (pull_isLB hQ _) hamp
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.trivial_locus_rigidified_bundle_closed_seesaw S (A ⊗ A) L₀ N hAA hL₀ hamp₀ hN hrig
  refine ⟨Z, i, hi, fun T t A' _ _ φ' φ₂' g g' hpb hsq hg hg' => ?_⟩
  have hpb₂ := GlobalTheory.WeilIntegral.isGrpPullback_prod hpb hpb hsq.1 hsq.2
  rw [← hZ T t (A' ⊗ A') φ₂' hpb₂, ← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, hc, map_sub, ← pull_comp,
    ← pull_comp, ← comm_left hsq f g hg, ← comm_right hsq f' g' hg', pull_comp, pull_comp, sub_eq_zero,
    ← cls_eq_iff (pull_isLB (pull_isLB hQ _) _) (pull_isLB (pull_isLB hQ _) _)]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemePullbackAdjointEndomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_pullback_adjoint_endomorphism_pair : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (f f' : A ⟶ A), IsMonHom f → IsMonHom f' → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (g g' : A' ⟶ A'), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → g.left ≫ φ' = φ' ≫ f.left → g'.left ≫ φ' = φ' ≫ f'.left → (LBIso ((Q.pull φ₂').pull (lift (fst A' A' ≫ g) (snd A' A')).left) ((Q.pull φ₂').pull (lift (fst A' A') (snd A' A' ≫ g')).left) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | exact @GlobalTheory.EndLoc.exists_closed_adj | exact GlobalTheory.EndLoc.exists_closed_adj | (intros; apply GlobalTheory.EndLoc.exists_closed_adj <;> assumption)
end
end
