module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyHomotopyFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialAlexanderWhitneyHomotopyEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeContractingHomotopy
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitSectionAvoid
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
open scoped Simplicial
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EZ.Cone

theorem homExt {m a : ℕ} {f g : ⦋m⦌ ⟶ ⦋a⦌}
    (h : ∀ j : Fin (m + 1), (f.toOrderHom j : ℕ) = g.toOrderHom j) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun j => Fin.ext (h j)))

def cv {n a : ℕ} (f : ⦋n⦌ ⟶ ⦋a⦌) : ⦋n + 1⦌ ⟶ ⦋a⦌ :=
  SimplexCategory.mkHom ⟨fun j => if h : (j : ℕ) = 0 then 0 else
      f.toOrderHom ⟨(j : ℕ) - 1, by have := j.2; change _ < n + 1; omega⟩, by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    dsimp only
    split_ifs with hi hj hj
    · exact le_refl _
    · exact Fin.zero_le _
    · omega
    · exact f.toOrderHom.monotone (show ((⟨(i : ℕ) - 1, _⟩ : Fin _) ≤ ⟨(j : ℕ) - 1, _⟩) from by
        rw [Fin.mk_le_mk]; omega)⟩

theorem cv_apply {n a : ℕ} (f : ⦋n⦌ ⟶ ⦋a⦌) (j : Fin (n + 2)) :
    ((cv f).toOrderHom j : ℕ) = if h : (j : ℕ) = 0 then 0 else
      (f.toOrderHom ⟨(j : ℕ) - 1, by have := j.2; change _ < n + 1; omega⟩ : ℕ) := by
  simp only [cv, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk]
  split_ifs <;> rfl

theorem fc_apply (n m i : ℕ) (j : Fin (m + 1)) :
    ((fc n m i).toOrderHom j : ℕ) = min n (faceFun i j) := rfl

theorem idc_apply (n m : ℕ) (j : Fin (m + 1)) :
    ((idc n m).toOrderHom j : ℕ) = min n j := rfl

theorem face_cone_identity_zero {m a : ℕ} (f : ⦋m⦌ ⟶ ⦋a⦌) : fc (m + 1) m 0 ≫ cv f = f := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply]
  have h1 : ((fc (m + 1) m 0).toOrderHom j : ℕ) = j + 1 := by
    rw [fc_apply]; unfold faceFun; have := j.2; split_ifs <;> omega
  rw [dite_eq_right (by omega)]
  congr 2; apply Fin.ext; simp only [h1]; omega

theorem fcs_cv {m a : ℕ} (f : ⦋m + 1⦌ ⟶ ⦋a⦌) (k : ℕ) :
    fc (m + 2) (m + 1) (k + 1) ≫ cv f = cv (fc (m + 1) m k ≫ f) := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply, cv_apply]
  have hj := j.2
  by_cases h0 : (j : ℕ) = 0
  · rw [dite_eq_left h0]
    have : ((fc (m + 2) (m + 1) (k + 1)).toOrderHom j : ℕ) = 0 := by
      rw [fc_apply]; unfold faceFun; split_ifs <;> omega
    rw [dite_eq_left this]
  · have h1 : ((fc (m + 2) (m + 1) (k + 1)).toOrderHom j : ℕ) ≠ 0 := by
      rw [fc_apply]; unfold faceFun; split_ifs <;> omega
    rw [dite_eq_right h1, dite_eq_right h0, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    congr 2; apply Fin.ext
    simp only [fc_apply]; unfold faceFun; split_ifs <;> omega

theorem face_cone_identity_one {a : ℕ} (f : ⦋0⦌ ⟶ ⦋a⦌) : fc 1 0 1 ≫ cv f = idc a 0 := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply, idc_apply]
  have hj := j.2
  have : ((fc 1 0 1).toOrderHom j : ℕ) = 0 := by
    rw [fc_apply]; unfold faceFun; split_ifs <;> omega
  rw [dite_eq_left this]; omega

theorem bop_comp {n m p q r s : ℕ} (α : ⦋p⦌ ⟶ ⦋n⦌) (β : ⦋q⦌ ⟶ ⦋m⦌) (α' : ⦋r⦌ ⟶ ⦋p⦌)
    (β' : ⦋s⦌ ⟶ ⦋q⦌) : bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have h := Free.single_comp_single ℤ (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op ⦋n⦌, op ⦋m⦌) ⟶ (op ⦋p⦌, op ⦋q⦌) from (α.op, β.op))
    (show (op ⦋p⦌, op ⦋q⦌) ⟶ (op ⦋r⦌, op ⦋s⦌) from (α'.op, β'.op)) 1 1
  rw [mul_one] at h
  exact h

def coneHom {a b n : ℕ} (x : (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n⦌, op ⦋n⦌)) :
    (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n + 1⦌, op ⦋n + 1⦌) :=
  ((cv x.1.unop).op, (cv x.2.unop).op)

def cone (a b n : ℕ) : (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)) :=
  Finsupp.mapDomain.addMonoidHom coneHom

def eps (a b : ℕ) : (bo a b ⟶ bo 0 0) →+ ℤ := Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

theorem cone_bop {a b n : ℕ} (α : ⦋n⦌ ⟶ ⦋a⦌) (β : ⦋n⦌ ⟶ ⦋b⦌) :
    cone a b n (bop α β) = bop (cv α) (cv β) := by
  exact Finsupp.mapDomain_single

theorem eps_bop {a b : ℕ} (α : ⦋0⦌ ⟶ ⦋a⦌) (β : ⦋0⦌ ⟶ ⦋b⦌) : eps a b (bop α β) = 1 := by
  exact Finsupp.liftAddHom_apply_single _ _ _

theorem single_eq {a b n p : ℕ} (x : (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n⦌, op ⦋p⦌)) (c : ℤ) :
    (Finsupp.single x c : bo a b ⟶ bo n p) = c • bop x.1.unop x.2.unop := by
  have h := map_zsmul (Finsupp.singleAddHom (M := ℤ) x) c (1 : ℤ)
  rw [smul_eq_mul, mul_one] at h
  exact h

theorem ind {a b n p : ℕ} (P : (bo a b ⟶ bo n p) → Prop) (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g))
    (hs : ∀ (α : ⦋n⦌ ⟶ ⦋a⦌) (β : ⦋p⦌ ⟶ ⦋b⦌) (c : ℤ), P (c • bop α β)) (r : bo a b ⟶ bo n p) : P r :=
  Finsupp.induction_linear r h0 hadd (fun x c => by have h := hs x.1.unop x.2.unop c; rw [← single_eq] at h; exact h)

theorem key {a b n : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋a⦌) (β : ⦋n + 1⦌ ⟶ ⦋b⦌) :
    cone a b (n + 1) (bop α β) ≫ dD (n + 2) (n + 1) = bop α β - cone a b n (bop α β ≫ dD (n + 1) n) := by
  rw [cone_bop]
  unfold dD
  rw [ite_eq_left rfl, ite_eq_left rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, cone_bop]
  rw [Finset.sum_range_succ' _ (n + 2)]
  have h0 : fc (n + 2) (n + 1) 0 ≫ cv α = α := face_cone_identity_zero α
  have h0' : fc (n + 2) (n + 1) 0 ≫ cv β = β := face_cone_identity_zero β
  simp only [h0, h0', fcs_cv, pow_succ, pow_zero, one_smul, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  abel

theorem key0 {a b : ℕ} (α : ⦋0⦌ ⟶ ⦋a⦌) (β : ⦋0⦌ ⟶ ⦋b⦌) :
    cone a b 0 (bop α β) ≫ dD 1 0 = bop α β - bop (idc a 0) (idc b 0) := by
  rw [cone_bop]
  unfold dD
  rw [ite_eq_left rfl]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, face_cone_identity_one]
  have h0 : fc 1 0 0 ≫ cv α = α := face_cone_identity_zero α
  have h0' : fc 1 0 0 ≫ cv β = β := face_cone_identity_zero β
  simp only [h0, h0', pow_zero, pow_one, one_smul, neg_smul, zero_add]
  abel

theorem coneContraction : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)))
    (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ),
    (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b),
      ε a b (bop α β) = 1) ∧
    (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧
    ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)),
      cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  refine ⟨cone, eps, fun a b α β => eps_bop α β, ?_, ?_⟩
  · intro a b r
    refine ind (P := fun r => cone a b 0 r ≫ dD 1 0 = r - eps a b r • bop (idc a 0) (idc b 0)) ?_ ?_ ?_ r
    · rw [map_zero, map_zero, Limits.zero_comp, zero_smul, sub_zero]
    · intro f g hf hg
      simp only [map_add (f := _), Preadditive.add_comp, add_smul, hf, hg]
      abel
    · intro α β c
      rw [map_zsmul, Preadditive.zsmul_comp, key0, map_zsmul, eps_bop, smul_sub, smul_eq_mul, mul_one]
  · intro a b n r
    refine ind (P := fun r => cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n))
      ?_ ?_ ?_ r
    · rw [map_zero, Limits.zero_comp, Limits.zero_comp, map_zero, sub_zero]
    · intro f g hf hg
      simp only [map_add (f := _), Preadditive.add_comp, hf, hg]
      abel
    · intro α β c
      rw [map_zsmul, Preadditive.zsmul_comp, key, Preadditive.zsmul_comp, map_zsmul, smul_sub]

end GlobalTheory.EZ.Cone
end
end

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_contracting_homotopy : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ), (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b), ε a b (bop α β) = 1) ∧ (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧ ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)), cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  first | (exact @GlobalTheory.EZ.Cone.coneContraction) | (exact GlobalTheory.EZ.Cone.coneContraction) | (intros; apply GlobalTheory.EZ.Cone.coneContraction  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCompShuffleHomotopicId
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCompShuffleHomotopicId
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ

theorem fc_succ_eq_δ (n i : ℕ) (hi : i < n + 2) :
    fc (n + 1) n i = SimplexCategory.δ (⟨i, hi⟩ : Fin (n + 2)) := by
  ext j
  simp [fc, clampHom, faceFun, SimplexCategory.δ, Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

def diagOp : SimplicialObject BOp := Functor.diag SimplexCategoryᵒᵖ ⋙ Free.embedding ℤ _

theorem dD_succ_eq_objD (n : ℕ) : dD (n + 1) n = AlternatingFaceMapComplex.objD diagOp n := by
  rw [dD, if_pos rfl, AlternatingFaceMapComplex.objD, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fc_succ_eq_δ n i i.2]
  rfl

theorem dD_comp_dD (n m k : ℕ) : dD n m ≫ dD m k = 0 := by
  by_cases h1 : n = m + 1
  · subst h1
    by_cases h2 : m = k + 1
    · subst h2
      rw [dD_succ_eq_objD, dD_succ_eq_objD]
      exact AlternatingFaceMapComplex.d_squared diagOp k
    · rw [show dD m k = 0 from if_neg h2, Limits.comp_zero]
  · rw [show dD n m = 0 from if_neg h1, Limits.zero_comp]

theorem awO_zero : awO 0 0 0 = 𝟙 (bo 0 0) := by
  rw [awO, if_pos rfl]
  have h1 : idc 0 0 = 𝟙 _ := Subsingleton.elim _ _
  have h2 : backc 0 0 0 = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, h2]
  rfl

def awThen (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) : bo n n ⟶ bo n n :=
  ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n

def awHtpy (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) :
    ∀ n : ℕ, bo n n ⟶ bo (n + 1) (n + 1) := fun n =>
  Nat.rec (motive := fun n => bo n n ⟶ bo (n + 1) (n + 1)) 0
    (fun k K => cone (k + 1) (k + 1) (k + 1) (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ K)) n

theorem awThen_comm (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (haw : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b) (n : ℕ) :
    awThen G (n + 1) ≫ dD (n + 1) n = dD (n + 1) n ≫ awThen G n := by
  simp only [awThen, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  have e1 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
      awO (n + 1) x.1 x.2 ≫ G x.1 x.2 (n + 1) ≫ dD (n + 1) n =
        ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n :=
    fun x hx => by rw [hG _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]
  have e2 : ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      dD (n + 1) n ≫ awO n y.1 y.2 ≫ G y.1 y.2 n =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n :=
    fun y hy => by
      rw [← Category.assoc, haw _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), Preadditive.sum_comp]
      simp only [Category.assoc]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]

theorem awHtpy_spec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (hG0 : G 0 0 0 = 𝟙 (bo 0 0))
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (haw : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b)
    (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)))
    (hcone : ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)),
      cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n)) :
    ∀ n : ℕ, awThen G (n + 1) = 𝟙 _ + awHtpy G cone (n + 1) ≫ dD (n + 1 + 1) (n + 1) +
      dD (n + 1) n ≫ awHtpy G cone n := by
  have h0 : awThen G 0 = 𝟙 _ := by
    simp [awThen, awO_zero, hG0]
  have key : ∀ k : ℕ,
      (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k) ≫ dD (k + 1) k = 0 →
      awThen G (k + 1) = 𝟙 _ + awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) +
        dD (k + 1) k ≫ awHtpy G cone k := by
    intro k hk
    have h := hcone (k + 1) (k + 1) k (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k)
    rw [hk, map_zero, sub_zero] at h
    have h' : awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) =
        awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k := h
    rw [h']
    abel
  intro n
  induction n with
  | zero =>
    apply key
    have hK : awHtpy G cone 0 = 0 := rfl
    rw [hK, Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw 0, h0]
    simp
  | succ j ih =>
    apply key
    rw [Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw (j + 1), ih,
      Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc (dD (j + 1 + 1) (j + 1)) (dD (j + 1) j),
      dD_comp_dD, Limits.zero_comp]
    simp only [Category.comp_id, Category.id_comp, Category.assoc, add_zero]
    abel

theorem awThen_homotopic : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) →
    (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) →
    ∃ H : ∀ n m : ℕ, bo n n ⟶ bo m m, ∀ n : ℕ,
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n =
        𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n := by
  intro G hG0 hG
  obtain ⟨cone, ε, -, -, hcone⟩ := GlobalTheory.T.cone_contracting_homotopy
  have haw := GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT
  refine ⟨fun n m => if h : m = n + 1 then awHtpy G cone n ≫ eqToHom (by rw [h]) else 0, fun n => ?_⟩
  cases n with
  | zero =>
    have h0 : awThen G 0 = 𝟙 _ := by
      simp [awThen, awO_zero, hG0]
    have hK : awHtpy G cone 0 = 0 := rfl
    change awThen G 0 = _
    simp [h0, hK, dD]
  | succ k =>
    change awThen G (k + 1) = _
    simp only [dif_pos, eqToHom_refl, Category.comp_id, Nat.add_sub_cancel]
    exact awHtpy_spec G hG0 hG haw cone hcone k

end GlobalTheory.EZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCompShuffleHomotopicIdStatement
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → ∃ H : ∀ n m : ℕ, bo n n ⟶ bo m m, ∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n := by
  first | (exact @GlobalTheory.EZ.awThen_homotopic) | (exact GlobalTheory.EZ.awThen_homotopic) | (intros; apply GlobalTheory.EZ.awThen_homotopic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBisimplicialShuffleOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBisimplicialShuffleOperators
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ.Shuf

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op (SimplexCategory.mk n), op (SimplexCategory.mk m)) ⟶
      (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) from (α.op, β.op))
    (show (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) ⟶
      (op (SimplexCategory.mk r), op (SimplexCategory.mk s)) from (α'.op, β'.op)) 1 1
  simp only [mul_one] at this
  exact this

theorem bop_id (n m : ℕ) : bop (𝟙 (SimplexCategory.mk n)) (𝟙 (SimplexCategory.mk m)) = 𝟙 (bo n m) := rfl

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = ((j : Fin (n + 1)) : ℕ)
  omega

theorem fc_comp_fc (n i j : ℕ) (hji : j < i) (hi : i ≤ n + 2) :
    fc (n + 1) n j ≫ fc (n + 2) (n + 1) i = fc (n + 1) n (i - 1) ≫ fc (n + 2) (n + 1) j := by
  ext k
  have hk : (k : ℕ) < n + 1 := k.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]
  split_ifs <;> omega

theorem alt_double_sum {M : Type*} [AddCommGroup M] (n : ℕ)
    (F : (SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 2)) → M) :
    ∑ i ∈ Finset.range (n + 3), ∑ j ∈ Finset.range (n + 2),
      ((-1 : ℤ) ^ i * (-1) ^ j) • F (fc (n + 1) n j ≫ fc (n + 2) (n + 1) i) = 0 := _root_.GlobalTheory.EZ.TotSq.alt_double_sum (M := M) n F

theorem dH_comp_dH (a b x y c d : ℕ) : dH a b x y ≫ dH x y c d = 0 := by
  unfold dH
  by_cases h1 : a = x + 1 ∧ b = y
  · by_cases h2 : x = c + 1 ∧ y = d
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum c (fun α => bop α (idc b b ≫ idc b b))
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dV_comp_dV (a b x y c d : ℕ) : dV a b x y ≫ dV x y c d = 0 := by
  unfold dV
  by_cases h1 : a = x ∧ b = y + 1
  · by_cases h2 : x = c ∧ y = d + 1
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum d (fun β => bop (idc a a ≫ idc a a) β)
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dH_comp_dV (c d : ℕ) :
    dH (c + 1) (d + 1) c (d + 1) ≫ dV c (d + 1) c d = dV (c + 1) (d + 1) (c + 1) d ≫ dH (c + 1) d c d := by
  unfold dH dV
  rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩,
    Preadditive.sum_comp, Preadditive.sum_comp]
  simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul,
    idc_self, Category.id_comp, Category.comp_id]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem dT_comp_dT (a b c d k : ℕ) (hk : c + d = k) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := _root_.GlobalTheory.EZ.TotSq.dT_comp_dT a b c d k hk

noncomputable def shufRec (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (n : ℕ) :
    ∀ a b : ℕ, bo a b ⟶ bo n n :=
  Nat.rec (motive := fun n => ∀ a b : ℕ, bo a b ⟶ bo n n) (fun a b => idO a b 0 0)
    (fun n g a b => if a + b = n + 1 then
      cone a b n (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ g x.1 x.2) else 0) n

theorem shufRec_zero (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (a b : ℕ) :
    shufRec cone 0 a b = idO a b 0 0 := rfl

theorem shufRec_succ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (n a b : ℕ) :
    shufRec cone (n + 1) a b = if a + b = n + 1 then
      cone a b n (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ shufRec cone n x.1 x.2) else 0 := rfl

theorem exists_shuffle : ∃ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) ∧
    ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n := by
  obtain ⟨cone, ε, hε, h0, hs⟩ := GlobalTheory.T.cone_contracting_homotopy
  have hid : shufRec cone 0 0 0 = 𝟙 (bo 0 0) := by
    rw [shufRec_zero]
    rw [idO, if_pos ⟨rfl, rfl⟩, idc_self]
    exact bop_id 0 0
  refine ⟨fun a b n => shufRec cone n a b, hid, ?_⟩
  intro a b n
  induction n generalizing a b with
  | zero =>
    intro hab
    dsimp only
    rw [shufRec_succ, if_pos hab, h0]
    have hr : ε a b (∑ x ∈ Finset.HasAntidiagonal.antidiagonal 0, dT a b x.1 x.2 ≫ shufRec cone 0 x.1 x.2) = 0 := by
      rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      dsimp only
      rw [hid, Category.comp_id]
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
      · simp [dT, dH, dV, Finset.sum_range_succ, map_add (f := _), map_zsmul, hε]
      · simp [dT, dH, dV, Finset.sum_range_succ, map_add (f := _), map_zsmul, hε]
    rw [hr, zero_smul, sub_zero]
  | succ n ih =>
    intro hab
    dsimp only at ih ⊢
    rw [shufRec_succ, if_pos hab, hs]
    have step : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
        (dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫ dD (n + 1) n =
          ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, (dT a b x.1 x.2 ≫ dT x.1 x.2 y.1 y.2) ≫
            shufRec cone n y.1 y.2 := by
      intro x hx
      rw [Category.assoc, ih x.1 x.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]
      simp only [Category.assoc]
    have hz : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫
        dD (n + 1) n = 0 := by
      rw [Preadditive.sum_comp, Finset.sum_congr rfl step, Finset.sum_comm]
      refine Finset.sum_eq_zero fun y hy => ?_
      rw [← Preadditive.sum_comp, dT_comp_dT a b y.1 y.2 n (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), zero_comp]
    rw [hz, map_zero, sub_zero]

end GlobalTheory.EZ.Shuf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBisimplicialShuffleOperatorsStatement
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bisimplicial_shuffle_operators : ∃ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) ∧ ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n := by
  first | (exact @GlobalTheory.EZ.Shuf.exists_shuffle) | (exact GlobalTheory.EZ.Shuf.exists_shuffle) | (intros; apply GlobalTheory.EZ.Shuf.exists_shuffle  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EilenbergZilberHomotopyEquivalence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairPowerSumValue
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.Ext
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

abbrev ext1 (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex (CochainComplex C ℤ) (ComplexShape.down ℕ) where
  X a := (K.X a).extend ComplexShape.embeddingDownNat
  d a b := HomologicalComplex.extendMap (K.d a b) ComplexShape.embeddingDownNat
  shape a b h := by rw [K.shape a b h, HomologicalComplex.extendMap_zero]
  d_comp_d' a b c _ _ := by rw [← HomologicalComplex.extendMap_comp, K.d_comp_d, HomologicalComplex.extendMap_zero]

abbrev ext2 (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (ext1 K).extend ComplexShape.embeddingDownNat

lemma fN (a : ℕ) : ComplexShape.embeddingDownNat.f a = -(a : ℤ) := by simp

variable (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))

def kX {p q : ℤ} {a b : ℕ}
    (ha : ComplexShape.embeddingDownNat.f a = p) (hb : ComplexShape.embeddingDownNat.f b = q) :
    ((ext2 K).X p).X q ≅ (K.X a).X b :=
  (HomologicalComplex.eval _ _ q).mapIso (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat ha) ≪≫
    HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat hb

lemma isZero_ext_of_pos {p q : ℤ} (h : 0 < p ∨ 0 < q) : IsZero (((ext2 K).X p).X q) := by
  rcases le_or_gt p 0 with hp | hp
  · have hq : 0 < q := by omega
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a:ℤ) := ⟨(-p).toNat, by omega⟩
    refine IsZero.of_iso ?_ ((HomologicalComplex.eval _ _ q).mapIso
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) (fN a)))
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)
  · exact (HomologicalComplex.eval _ _ q).map_isZero
      (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega))

abbrev kN (a b : ℕ) : ((ext2 K).X (-(a : ℤ))).X (-(b : ℤ)) ≅ (K.X a).X b :=
  kX K (p := -(a : ℤ)) (q := -(b : ℤ)) (a := a) (b := b) (fN a) (fN b)

lemma kN_hom (a b : ℕ) :
    (kN K a b).hom = (HomologicalComplex.extendXIso
      (ext1 K)
      ComplexShape.embeddingDownNat (i := a) (i' := -(a : ℤ)) (fN _)).hom.f (-(b : ℤ)) ≫
      (HomologicalComplex.extendXIso (K.X a) ComplexShape.embeddingDownNat (i := b) (i' := -(b : ℤ)) (fN _)).hom := rfl

lemma kX_d₁ (a b : ℕ) :
    ((ext2 K).d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ))).f (-(b : ℤ)) ≫ (kN K a b).hom =
      (kN K (a + 1) b).hom ≫ (K.d (a + 1) a).f b := by
  have h := HomologicalComplex.extend_d_eq
    (ext1 K)
    ComplexShape.embeddingDownNat (i := a + 1) (j := a) (i' := -((a + 1 : ℕ) : ℤ)) (j' := -(a : ℤ)) (fN _) (fN _)
  have hh := HomologicalComplex.extendMap_f (K.d (a + 1) a) ComplexShape.embeddingDownNat (i := b) (i' := -(b:ℤ)) (fN _)
  rw [h, kN_hom, kN_hom]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  have e1 : ∀ {A B : CochainComplex C ℤ} (φ : A ≅ B) (n : ℤ), φ.inv.f n ≫ φ.hom.f n = 𝟙 _ := fun φ n => by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [reassoc_of% (e1 _ (-(b : ℤ)))]
  rw [hh]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma kX_d₂ (a b : ℕ) :
    ((ext2 K).X (-(a : ℤ))).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) ≫ (kN K a b).hom =
      (kN K a (b + 1)).hom ≫ (K.X a).d (b + 1) b := by
  have := HomologicalComplex.Hom.comm (HomologicalComplex.extendXIso
    (ext1 K)
    ComplexShape.embeddingDownNat (i := a) (i' := -(a:ℤ)) (fN _)).hom (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ))
  have h2 := HomologicalComplex.extend_d_eq (K.X a) ComplexShape.embeddingDownNat (i := b + 1) (j := b)
    (i' := -((b + 1 : ℕ) : ℤ)) (j' := -(b : ℤ)) (fN _) (fN _)
  rw [kN_hom, kN_hom]
  have e := this =≫ (HomologicalComplex.extendXIso (K.X a) ComplexShape.embeddingDownNat (i := b) (i' := -(b:ℤ)) (fN _)).hom
  simp only [Category.assoc] at e
  rw [← e, h2]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Tot
variable [K.HasTotal (ComplexShape.down ℕ)] [(ext2 K).HasTotal (ComplexShape.up ℤ)]

def cmp {p q n : ℤ} (a b m : ℕ) (ha : ComplexShape.embeddingDownNat.f a = p)
    (hb : ComplexShape.embeddingDownNat.f b = q) (hm : ComplexShape.embeddingDownNat.f m = n)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a, b) = m) :
    ((ext2 K).X p).X q ⟶ ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n :=
  (kX K ha hb).hom ≫ K.ιTotal (ComplexShape.down ℕ) a b m h ≫
    ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat hm).inv

lemma cmp_congr {p q n : ℤ} (a b m a' b' m' : ℕ) (ha : ComplexShape.embeddingDownNat.f a = p)
    (hb : ComplexShape.embeddingDownNat.f b = q) (hm : ComplexShape.embeddingDownNat.f m = n)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a, b) = m)
    (ha' : ComplexShape.embeddingDownNat.f a' = p)
    (hb' : ComplexShape.embeddingDownNat.f b' = q) (hm' : ComplexShape.embeddingDownNat.f m' = n)
    (h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a', b') = m') :
    cmp K a b m ha hb hm h = cmp K a' b' m' ha' hb' hm' h' := by
  obtain rfl : a = a' := ComplexShape.embeddingDownNat.injective_f (ha.trans ha'.symm)
  obtain rfl : b = b' := ComplexShape.embeddingDownNat.injective_f (hb.trans hb'.symm)
  obtain rfl : m = m' := ComplexShape.embeddingDownNat.injective_f (hm.trans hm'.symm)
  rfl

def homF (n : ℤ) : ((ext2 K).total (ComplexShape.up ℤ)).X n ⟶
    ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n :=
  (ext2 K).totalDesc (fun p q h =>
    if hpq : p ≤ 0 ∧ q ≤ 0 then
      cmp K (-p).toNat (-q).toNat (-n).toNat (by simp; omega) (by simp; omega)
        (by simp only [ComplexShape.π_def] at h; simp; omega)
        (by simp only [ComplexShape.π_def] at h ⊢; omega)
    else 0)

lemma ι_homF (a b m : ℕ) (h : a + b = m) :
    (ext2 K).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(m : ℤ)) (by simp only [ComplexShape.π_def]; omega) ≫
      homF K (-(m : ℤ)) =
    (kN K a b).hom ≫ K.ιTotal (ComplexShape.down ℕ) a b m h ≫
      ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN m)).inv := by
  rw [homF, HomologicalComplex₂.ι_totalDesc, dite_eq_left (by omega)]
  exact cmp_congr K _ _ _ a b m _ _ _ _ (fN a) (fN b) (fN m) h

def invC {n : ℤ} (m : ℕ) (hm : ComplexShape.embeddingDownNat.f m = n) :
    ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n ⟶
      ((ext2 K).total (ComplexShape.up ℤ)).X n :=
  ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat hm).hom ≫
    K.totalDesc (fun a b h => (kN K a b).inv ≫ (ext2 K).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) n
      (by simp only [ComplexShape.π_def] at h ⊢; simp at hm; omega))

lemma invC_congr {n : ℤ} (m m' : ℕ) (hm : ComplexShape.embeddingDownNat.f m = n)
    (hm' : ComplexShape.embeddingDownNat.f m' = n) : invC K m hm = invC K m' hm' := by
  obtain rfl : m = m' := ComplexShape.embeddingDownNat.injective_f (hm.trans hm'.symm)
  rfl

def invF (n : ℤ) : ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n ⟶
    ((ext2 K).total (ComplexShape.up ℤ)).X n :=
  if hn : n ≤ 0 then invC K (-n).toNat (by simp; omega) else 0

lemma ι_invF (a b m : ℕ) (h : a + b = m) :
    K.ιTotal (ComplexShape.down ℕ) a b m h ≫
      ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN m)).inv ≫ invF K (-(m : ℤ)) =
    (kN K a b).inv ≫ (ext2 K).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(m : ℤ))
      (by simp only [ComplexShape.π_def]; omega) := by
  rw [invF, dite_eq_left (by omega), invC_congr K _ m _ (fN m), invC, Iso.inv_hom_id_assoc,
    HomologicalComplex₂.ι_totalDesc]

end Tot

section Tot2
variable [K.HasTotal (ComplexShape.down ℕ)] [(ext2 K).HasTotal (ComplexShape.up ℤ)]

lemma homF_invF (n : ℤ) : homF K n ≫ invF K n = 𝟙 _ := by
  ext p q h
  by_cases hpq : p ≤ 0 ∧ q ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a:ℤ) := ⟨(-p).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, q = -(b:ℤ) := ⟨(-q).toNat, by omega⟩
    obtain rfl : n = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at h; omega
    rw [reassoc_of% (ι_homF K a b (a + b) rfl), ι_invF K a b (a + b) rfl,
      Iso.hom_inv_id_assoc, Category.comp_id]
  · exact (isZero_ext_of_pos K (by omega)).eq_of_src _ _

lemma invF_homF (n : ℤ) : invF K n ≫ homF K n = 𝟙 _ := by
  by_cases hn : n ≤ 0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m:ℤ) := ⟨(-n).toNat, by omega⟩
    rw [← cancel_epi ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN m)).inv]
    ext a b h
    rw [reassoc_of% (ι_invF K a b m h), ι_homF K a b m h, Iso.inv_hom_id_assoc, Category.comp_id]
  · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)).eq_of_src _ _

lemma negOnePow_negNat (a : ℕ) : (-(a : ℤ)).negOnePow = (-1 : ℤˣ) ^ a := by
  rw [Int.negOnePow_neg, Int.negOnePow_def, zpow_natCast]

lemma homF_comm (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    homF K i ≫ ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).d i j =
      ((ext2 K).total (ComplexShape.up ℤ)).d i j ≫ homF K j := by
  change i + 1 = j at hij
  ext p q h
  by_cases hpq : p ≤ 0 ∧ q ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a:ℤ) := ⟨(-p).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, q = -(b:ℤ) := ⟨(-q).toNat, by omega⟩
    obtain rfl : i = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at h; omega
    rcases Nat.eq_zero_or_pos (a + b) with hab | hab
    · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)).eq_of_tgt _ _
    obtain ⟨k, hk⟩ : ∃ k, a + b = k + 1 := ⟨a + b - 1, by omega⟩
    obtain rfl : j = -(k : ℤ) := by omega
    rw [reassoc_of% (ι_homF K a b (a + b) rfl),
      HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat (i := a + b) (j := k) (fN _) (fN _),
      Iso.inv_hom_id_assoc]
    simp only [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
    have hd₁ : (kN K a b).hom ≫ K.d₁ (ComplexShape.down ℕ) a b k ≫
        ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN k)).inv =
        (ext2 K).d₁ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(k : ℤ)) ≫ homF K (-(k : ℤ)) := by
      rcases a with _ | a'
      · rw [K.d₁_eq_zero _ _ _ _ (by intro hr; change _ + 1 = 0 at hr; omega),
          (ext2 K).d₁_eq' _ (i₁' := 1) (by simp only [ComplexShape.up_Rel]; omega) _ _,
          (isZero_ext_of_pos K (p := 1) (q := -(b:ℤ)) (Or.inl one_pos)).eq_of_src
            ((ext2 K).ιTotalOrZero (ComplexShape.up ℤ) 1 (-(b : ℤ)) (-(k : ℤ))) 0]
        simp
      · rw [K.d₁_eq _ (i₁' := a') rfl _ _ (by simp only [ComplexShape.π_def]; omega),
          (ext2 K).d₁_eq _ (i₁' := -(a' : ℤ)) (by simp only [ComplexShape.up_Rel]; omega) _ _
            (by simp only [ComplexShape.π_def]; omega)]
        have e1 : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a' + 1, b) = 1 := rfl
        have e2 : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (-((a' + 1 : ℕ) : ℤ), -(b : ℤ)) = 1 := rfl
        rw [e1, e2, one_smul, one_smul, Category.assoc, Category.assoc, ι_homF K a' b k (by omega),
          reassoc_of% (kX_d₁ K a' b)]
    have hd₂ : (kN K a b).hom ≫ K.d₂ (ComplexShape.down ℕ) a b k ≫
        ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN k)).inv =
        (ext2 K).d₂ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(k : ℤ)) ≫ homF K (-(k : ℤ)) := by
      rcases b with _ | b'
      · rw [K.d₂_eq_zero _ _ _ _ (by intro hr; change _ + 1 = 0 at hr; omega),
          (ext2 K).d₂_eq' _ _ (i₂' := 1) (by simp only [ComplexShape.up_Rel]; omega) _,
          (isZero_ext_of_pos K (p := -(a : ℤ)) (q := 1) (Or.inr one_pos)).eq_of_src
            ((ext2 K).ιTotalOrZero (ComplexShape.up ℤ) (-(a : ℤ)) 1 (-(k : ℤ))) 0]
        simp
      · rw [K.d₂_eq _ _ (i₂' := b') rfl _ (by simp only [ComplexShape.π_def]; omega),
          (ext2 K).d₂_eq _ _ (i₂' := -(b' : ℤ)) (by simp only [ComplexShape.up_Rel]; omega) _
            (by simp only [ComplexShape.π_def]; omega)]
        have e1 : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a, b' + 1) =
          (-1 : ℤˣ) ^ a := rfl
        have e2 : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (-(a : ℤ), -((b' + 1 : ℕ) : ℤ)) = (-(a : ℤ)).negOnePow := rfl
        rw [e1, e2, negOnePow_negNat, Linear.units_smul_comp, Linear.units_smul_comp, Linear.comp_units_smul,
          Category.assoc, Category.assoc, ι_homF K a b' k (by omega), reassoc_of% (kX_d₂ K a b')]
    rw [hd₁, hd₂]
  · exact (isZero_ext_of_pos K (by omega)).eq_of_src _ _

end Tot2

section Tot3
variable [K.HasTotal (ComplexShape.down ℕ)] [(ext2 K).HasTotal (ComplexShape.up ℤ)]

def totIso : (ext2 K).total (ComplexShape.up ℤ) ≅ (K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents (fun n => ⟨homF K n, invF K n, homF_invF K n, invF_homF K n⟩)
    (fun i j h => homF_comm K i j h)

lemma totIso_inv_f (n : ℤ) : (totIso K).inv.f n = invF K n := rfl

end Tot3

def extHE {A B : ChainComplex C ℕ} (e : HomotopyEquiv A B) :
    HomotopyEquiv (A.extend ComplexShape.embeddingDownNat) (B.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap e.hom ComplexShape.embeddingDownNat
  inv := HomologicalComplex.extendMap e.inv ComplexShape.embeddingDownNat
  homotopyHomInvId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((e.homotopyHomInvId.extend ComplexShape.embeddingDownNat).trans
      (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((e.homotopyInvHomId.extend ComplexShape.embeddingDownNat).trans
      (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

section Sheaves
open GlobalTheory.EtC
variable (R : Type) [CommRing R]

def diagSIso (X : SimplicialObject Spc) :
    ((SimplicialObject.whiskering _ _).obj (free R)).obj (bidiag.obj X) ≅ GlobalTheory.EZ.diag.obj ((freeBi R).obj X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact ((free R).map_comp _ _))

def diagIso (X : SimplicialObject Spc) :
    (chains R).obj (bidiag.obj X) ≅ (diagCx ((freeBi R).obj X)).extend ComplexShape.embeddingDownNat :=
  (ComplexShape.embeddingDownNat.extendFunctor _).mapIso ((alternatingFaceMapComplex _).mapIso (diagSIso R X))

set_option backward.isDefEq.respectTransparency false in
lemma diagIso_hom_f (X : SimplicialObject Spc) (n : ℕ) :
    (diagIso R X).hom.f (-(n : ℤ)) = (chainsXIso R (bidiag.obj X) n).hom ≫
      ((diagCx ((freeBi R).obj X)).extendXIso ComplexShape.embeddingDownNat (fN n)).inv := by
  change (HomologicalComplex.extendMap ((alternatingFaceMapComplex _).map (diagSIso R X).hom)
    ComplexShape.embeddingDownNat).f (-(n:ℤ)) = _
  rw [HomologicalComplex.extendMap_f _ _ (fN n)]
  have h1 : ((alternatingFaceMapComplex (Shv R)).map (diagSIso R X).hom).f n = 𝟙 _ := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_map_f]; rfl
  rw [h1, Category.id_comp]
  rfl

lemma ev_awO (X : SimplicialObject Spc) (n a : ℕ) (ha : a ≤ n) :
    (ev ((freeBi R).obj X)).map (awO n a (n - a)) = (free R).map (awP X n a (n - a)) := by
  rw [awO, if_pos (by omega), ev_map_bop, awP]
  exact ((free R).map_comp _ _).symm

end Sheaves


set_option backward.isDefEq.respectTransparency false in
theorem homotopyEquiv_chains_totChains : ∀ (R : Type) [CommRing R] (X : SimplicialObject GlobalTheory.EtC.Spc), (∃ e : HomotopyEquiv (diagCx ((freeBi R).obj X)) (tot ((freeBi R).obj X)), ∀ n : ℕ, e.hom.f n = awF _ n) → ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X), ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n := by
  intro R _ X ⟨e, he⟩
  haveI : (ext2 (dbl ((freeBi R).obj X))).HasTotal (ComplexShape.up ℤ) := hasTotal_biChains R X
  refine ⟨(HomotopyEquiv.ofIso (diagIso R X)).trans ((extHE e).trans
    (HomotopyEquiv.ofIso (totIso (dbl ((freeBi R).obj X))).symm)), fun n => ?_⟩
  change (diagIso R X).hom.f (-(n:ℤ)) ≫ (HomologicalComplex.extendMap e.hom ComplexShape.embeddingDownNat).f (-(n:ℤ)) ≫
    (totIso (dbl ((freeBi R).obj X))).inv.f (-(n:ℤ)) = _
  rw [diagIso_hom_f, HomologicalComplex.extendMap_f _ _ (fN n), he n, totIso_inv_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [awZ, awF]
  congr 1
  simp only [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := ι_invF (dbl ((freeBi R).obj X)) (a : ℕ) (n - a) n (by omega)
  rw [Category.assoc, ev_awO R X n a (by omega)]
  exact (congrArg ((GlobalTheory.EtC.free R).map (awP X n a (n - a)) ≫ ·) h).trans rfl
end GlobalTheory.EZ.Ext
end
end

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eilenberg_zilber_homotopy_equivalence : ∀ (R : Type) [CommRing R] (X : SimplicialObject GlobalTheory.EtC.Spc), (∃ e : HomotopyEquiv (diagCx ((freeBi R).obj X)) (tot ((freeBi R).obj X)), ∀ n : ℕ, e.hom.f n = awF _ n) → ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X), ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n := by
  first | (exact @GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (exact GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (intros; apply GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains <;> assumption)
end

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology

namespace GlobalTheory.EZ
universe u v

theorem ez_nat {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
    (Y : SimplicialObject (SimplicialObject C)) :
    ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  obtain ⟨G, h0, hG⟩ := GlobalTheory.T.exists_bisimplicial_shuffle_operators
  obtain ⟨H, hH⟩ := GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id G h0 hG
  obtain ⟨K, hK⟩ := GlobalTheory.T.alexander_whitney_homotopy_formula G h0 hG
  exact GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv Y G H K h0 hG hH hK

variable (R : Type) [CommRing R]

theorem ez (X : SimplicialObject GlobalTheory.EtC.Spc) :
    ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X),
      ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n :=
  GlobalTheory.T.eilenberg_zilber_homotopy_equivalence R X (ez_nat _)

def ezEquiv (X : SimplicialObject GlobalTheory.EtC.Spc) :
    HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X) := (ez R X).choose

def awChains (X : SimplicialObject GlobalTheory.EtC.Spc) : (GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X) ⟶ totChains R X :=
  (ezEquiv R X).hom

theorem awChains_f (X : SimplicialObject GlobalTheory.EtC.Spc) (n : ℕ) : (awChains R X).f (-(n : ℤ)) = awZ R X n :=
  (ez R X).choose_spec n

theorem pull_awChains_bijective (X : SimplicialObject GlobalTheory.EtC.Spc) (I : GlobalTheory.EtC.Cx R) (k : ℤ) :
    Function.Bijective (GlobalTheory.EtC.cpull (awChains R X) I k) :=
  GlobalTheory.EtC.LevelCmp.cpull_bij_of_heq (ezEquiv R X) I k

end GlobalTheory.EZ
