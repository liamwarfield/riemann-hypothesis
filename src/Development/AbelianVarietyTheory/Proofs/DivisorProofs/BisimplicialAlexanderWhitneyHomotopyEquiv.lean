module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDifferentialEval
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialDoubleComplexDifferentials
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ

theorem fc_eq_δ (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  ext j
  simp only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.coe_mk, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rcases Fin.lt_or_le (Fin.castSucc j) i with hj | hj
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    have : (j : ℕ) < i := hj
    simp only [this, if_true, Fin.coe_castSucc]
    have := j.isLt
    simp only [SimplexCategory.len_mk] at this ⊢
    omega
  · rw [Fin.succAbove_of_le_castSucc _ _ hj]
    have : ¬ (j : ℕ) < i := by simpa [Fin.le_iff_val_le_val] using hj
    simp only [this, if_false, Fin.val_succ]
    have := j.isLt
    simp only [SimplexCategory.len_mk] at this ⊢
    omega

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp [idc, clampHom, SimplexCategory.mkHom]
  omega

theorem hsum_f {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} {α : Type} (s : Finset α) (f : α → (K ⟶ L)) (i : ι) :
    (∑ x ∈ s, f x).f i = ∑ x ∈ s, (f x).f i :=
  (HomologicalComplex.eval C c i).map_sum f s

section
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem dbl_d_f (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).d (a + 1) a).f b = (ev Y).map (dH (a + 1) b a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dH, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
    idc_self, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Finset.sum_range]
  dsimp only [dbl, alternatingFaceMapComplex]
  rw [AlternatingFaceMapComplex.obj_d_eq, hsum_f]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [HomologicalComplex.zsmul_f_apply, fc_eq_δ]
  rfl

theorem dbl_X_d (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).X a).d (b + 1) b = (ev Y).map (dV a (b + 1) a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dV, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
    idc_self, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [Finset.sum_range]
  change (AlternatingFaceMapComplex.obj (Y.obj (op (SimplexCategory.mk a)))).d (b + 1) b = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fc_eq_δ]
  rfl

variable [HasFiniteCoproducts C]

theorem ιTotal_D₁ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₁ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dH a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  rw [HomologicalComplex₂.ι_D₁]
  rcases a with _ | a
  · rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (0 = x.1.1 + 1 ∧ b = x.1.2) := by omega
    simp only [dH, hx, if_false, Functor.map_zero]
    exact zero_comp
  · rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℕ).Rel (a + 1) a from rfl) b k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_d_f]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a + 1 = x1 + 1 ∧ b = x2) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h2
        have : x1 = a := by omega
        subst this
        rfl
      simp only [dH, this, if_false, Functor.map_zero]
      exact zero_comp
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

theorem ιTotal_D₂ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₂ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, ((-1 : ℤ) ^ a) • ((ev Y).map (dV a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2)) := by
  rw [HomologicalComplex₂.ι_D₂]
  rcases b with _ | b
  · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (a = x.1.1 ∧ 0 = x.1.2 + 1) := by omega
    simp only [dV, hx, if_false, Functor.map_zero]
    exact (congrArg _ zero_comp).trans (zsmul_zero _)
  · rw [HomologicalComplex₂.d₂_eq _ _ a (show (ComplexShape.down ℕ).Rel (b + 1) b from rfl) k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_X_d]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a = x1 ∧ b + 1 = x2 + 1) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h1
        have : x2 = b := by omega
        subst this
        rfl
      simp only [dV, this, if_false, Functor.map_zero]
      exact (congrArg _ zero_comp).trans (zsmul_zero _)
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

theorem ιTotal_tot_d (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ)
    (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (tot Y).d (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  change _ ≫ ((dbl Y).total (ComplexShape.down ℕ)).d (k + 1) k = _
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add, ιTotal_D₁ Y a b k h, ιTotal_D₂ Y a b k h]
  refine Eq.trans Finset.sum_add_distrib.symm (Finset.sum_congr rfl (fun x _ => ?_))
  rw [dT, (ev Y).map_add, (ev Y).map_zsmul]
  first
    | (rw [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (simp only [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (erw [Preadditive.add_comp, Preadditive.zsmul_comp])
  rfl

end

end GlobalTheory.EZ
end
end

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.total_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  first | (exact @GlobalTheory.EZ.ιTotal_tot_d) | (exact GlobalTheory.EZ.ιTotal_tot_d) | (intros; apply GlobalTheory.EZ.ιTotal_tot_d <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalDifferentialEval
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousClassSubstitution
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

namespace GlobalTheory.EZ

theorem fc_succ_eq_delta (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min (n + 1) (if (j : ℕ) < i then (j : ℕ) else j + 1) = ((Fin.succAbove i j : Fin (n+2)) : ℕ)
  rcases lt_or_ge (j : ℕ) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h] <;> omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    simp [show ¬ (j : ℕ) < i by omega] <;> omega

theorem ev_map_dD_eq_diagCx_d {C : Type u} [Category.{v} C] [Preadditive C]
    (Y : SimplicialObject (SimplicialObject C)) (n : ℕ) :
    (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  refine Eq.trans ?_ (AlternatingFaceMapComplex.obj_d_eq (diag.obj Y) n).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dD, if_pos rfl, Functor.map_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Functor.map_zsmul, ev_map_bop, fc_succ_eq_delta]
  rfl

end GlobalTheory.EZ
end

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] (Y : SimplicialObject (SimplicialObject C)) (n : ℕ), (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  first | (exact @GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (exact GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (intros; apply GlobalTheory.EZ.ev_map_dD_eq_diagCx_d <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialAlexanderWhitneyHomotopyEquiv
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.AWEq

open Finset HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  (Y : SimplicialObject (SimplicialObject C))

theorem awop' : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT
theorem evd' : ∀ {C : Type u} [Category.{v} C] [Preadditive C] (Y : SimplicialObject (SimplicialObject C)) (n : ℕ), (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := @GlobalTheory.T.diagonal_differential_eval
theorem totd' : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := @GlobalTheory.T.total_differential_eval

abbrev ιz (a b n : ℕ) : ((dbl Y).X a).X b ⟶ (tot Y).X n := (dbl Y).ιTotalOrZero (ComplexShape.down ℕ) a b n

theorem ιz_eq (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n = (dbl Y).ιTotal (ComplexShape.down ℕ) a b n (by simpa only [ComplexShape.π_def] using h) :=
  (dbl Y).ιTotalOrZero_eq _ _ _ _ _

theorem ιz_ne (a b n : ℕ) (h : a + b ≠ n) : ιz Y a b n = 0 :=
  (dbl Y).ιTotalOrZero_eq_zero _ _ _ _ (by simpa only [ComplexShape.π_def] using h)

theorem dT_eq_zero (a b a' b' : ℕ) (h : a + b ≠ a' + b' + 1) : dT a b a' b' = 0 := by
  unfold dT dH dV
  rw [if_neg (by omega), if_neg (by omega), smul_zero, add_zero]

theorem awF_eq (n : ℕ) :
    awF Y n = ∑ x ∈ antidiagonal n, (ev Y).map (awO n x.1 x.2) ≫ ιz Y x.1 x.2 n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
  unfold awF
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ιz_eq Y _ _ _ (by omega)]

theorem ιz_d (a b k : ℕ) :
    ιz Y a b (k + 1) ≫ (tot Y).d (k + 1) k =
      ∑ x ∈ antidiagonal k, (ev Y).map (dT a b x.1 x.2) ≫ ιz Y x.1 x.2 k := by
  by_cases h : a + b = k + 1
  · rw [ιz_eq Y _ _ _ h, totd' Y a b k h, ← Finset.sum_attach (antidiagonal k)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ιz_eq Y _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 x.2)]
  · rw [ιz_ne Y _ _ _ h, zero_comp]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [dT_eq_zero a b x.1 x.2 (by omega), Functor.map_zero, zero_comp]

def shufF (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) : (tot Y).X n ⟶ (diagCx Y).X n :=
  (dbl Y).totalDesc (c₁₂ := ComplexShape.down ℕ) (fun a b _ => (ev Y).map (G a b n))

theorem ιz_shufF (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n ≫ shufF Y G n = (ev Y).map (G a b n) := by
  rw [ιz_eq Y _ _ _ h, shufF, ι_totalDesc]

theorem shufF_comm (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) (n : ℕ) :
    (tot Y).d (n + 1) n ≫ shufF Y G n = shufF Y G (n + 1) ≫ (diagCx Y).d (n + 1) n := by
  refine total.hom_ext (K := dbl Y) (c₁₂ := ComplexShape.down ℕ) (fun a b h => ?_)
  simp only [ComplexShape.π_def] at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← ιz_eq Y _ _ _ h, ← Category.assoc, ιz_d, Preadditive.sum_comp, ← Category.assoc, ιz_shufF Y G _ _ _ h,
    ← evd', ← Functor.map_comp, hG a b n h, Functor.map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Category.assoc, ιz_shufF Y G _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 hx), Functor.map_comp]

end GlobalTheory.EZ.AWEq

noncomputable section
namespace GlobalTheory.EZ.AWEq

open Finset HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  (Y : SimplicialObject (SimplicialObject C))

theorem awF_comm (n : ℕ) : awF Y (n + 1) ≫ (tot Y).d (n + 1) n = (diagCx Y).d (n + 1) n ≫ awF Y n := by
  rw [awF_eq, awF_eq, Preadditive.sum_comp, Preadditive.comp_sum, ← evd']
  simp_rw [Category.assoc, ιz_d, Preadditive.comp_sum]
  simp_rw [← Category.assoc, ← Functor.map_comp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [awop' n y.1 y.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 hy), Functor.map_sum, Preadditive.sum_comp]

theorem awF_shufF (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) :
    awF Y n ≫ shufF Y G n = (ev Y).map (∑ x ∈ antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [awF_eq, Preadditive.sum_comp, Functor.map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Category.assoc, ιz_shufF Y G _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 hx), Functor.map_comp]

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp [idc, clampHom]
  exact Nat.le_of_lt_succ j.2

theorem ev_idO_self (a b : ℕ) : (ev Y).map (idO a b a b) = 𝟙 _ := by
  unfold idO
  rw [if_pos ⟨rfl, rfl⟩, ev_map_bop, idc_self, idc_self]
  simp
  rfl

theorem sum_idO (a b n : ℕ) (h : a + b = n) :
    ∑ y ∈ antidiagonal n, (ev Y).map (idO a b y.1 y.2) ≫ ιz Y y.1 y.2 n = ιz Y a b n := by
  rw [Finset.sum_eq_single (a, b)]
  · rw [ev_idO_self, Category.id_comp]
  · intro y _ hy
    unfold idO
    rw [if_neg (fun h' => hy (Prod.ext h'.1.symm h'.2.symm)), Functor.map_zero, zero_comp]
  · intro hy
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 h) hy

def homD (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (i j : ℕ) : (diagCx Y).X i ⟶ (diagCx Y).X j :=
  if i + 1 = j then (ev Y).map (H i j) else 0

def homT (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (i j : ℕ) : (tot Y).X i ⟶ (tot Y).X j :=
  if i + 1 = j then
    (dbl Y).totalDesc (c₁₂ := ComplexShape.down ℕ)
      (fun a b _ => ∑ x ∈ antidiagonal j, (ev Y).map (K a b x.1 x.2) ≫ ιz Y x.1 x.2 j)
  else 0

theorem ιz_homT (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n ≫ homT Y K n (n + 1) =
      ∑ x ∈ antidiagonal (n + 1), (ev Y).map (K a b x.1 x.2) ≫ ιz Y x.1 x.2 (n + 1) := by
  rw [homT, if_pos rfl, ιz_eq Y _ _ _ h, ι_totalDesc]

theorem ιz_dNext (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n ≫ dNext n (homT Y K) =
      ∑ x ∈ antidiagonal n, ∑ j ∈ antidiagonal (n - 1),
        (ev Y).map (dT a b j.1 j.2 ≫ K j.1 j.2 x.1 x.2) ≫ ιz Y x.1 x.2 n := by
  cases n with
  | zero =>
    rw [Homotopy.dNext_zero_chainComplex, Limits.comp_zero]
    refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun j hj => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hj
    rw [dT_eq_zero a b j.1 j.2 (by omega), Limits.zero_comp, Functor.map_zero, Limits.zero_comp]
  | succ m =>
    rw [Homotopy.dNext_succ_chainComplex, ← Category.assoc, ιz_d, Preadditive.sum_comp, Nat.add_sub_cancel]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Category.assoc, ιz_homT Y K _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 hj), Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Category.assoc, ← Functor.map_comp]

end GlobalTheory.EZ.AWEq

noncomputable section
namespace GlobalTheory.EZ.AWEq

open Finset HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  (Y : SimplicialObject (SimplicialObject C))

def awC : diagCx Y ⟶ tot Y where
  f := awF Y
  comm' := by
    rintro i j (rfl : j + 1 = i)
    exact awF_comm Y j

def shufC (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) : tot Y ⟶ diagCx Y where
  f := shufF Y G
  comm' := by
    rintro i j (rfl : j + 1 = i)
    exact (shufF_comm Y G hG j).symm

def htpyD (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (H : ∀ n m : ℕ, bo n n ⟶ bo m m)
    (hH : ∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n =
      𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) :
    Homotopy (awC Y ≫ shufC Y G hG) (𝟙 (diagCx Y)) where
  hom := homD Y H
  zero i j hij := if_neg hij
  comm n := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, Homotopy.prevD_chainComplex]
    change awF Y n ≫ shufF Y G n = _
    rw [awF_shufF, hH n]
    simp only [Functor.map_add (ev Y), Functor.map_id, Functor.map_comp]
    rw [evd', homD, if_pos rfl, show (ev Y).map (𝟙 (bo n n)) = 𝟙 ((diagCx Y).X n) from (ev Y).map_id _]
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex]
      have : dD 0 (0 - 1) = 0 := by simp [dD]
      rw [this, Functor.map_zero, zero_comp, add_zero]
      abel
    | succ m =>
      rw [Homotopy.dNext_succ_chainComplex, Nat.add_sub_cancel, evd', homD, if_pos rfl]
      abel

def htpyT (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b')
    (hK : ∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' +
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') :
    Homotopy (shufC Y G hG ≫ awC Y) (𝟙 (tot Y)) where
  hom := homT Y K
  zero i j hij := if_neg hij
  comm n := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, Homotopy.prevD_chainComplex]
    change shufF Y G n ≫ awF Y n = _
    refine total.hom_ext (K := dbl Y) (c₁₂ := ComplexShape.down ℕ) (fun a b h => ?_)
    simp only [ComplexShape.π_def] at h
    rw [← ιz_eq Y _ _ _ h]
    subst h

    rw [← Category.assoc, ιz_shufF Y G _ _ _ rfl, awF_eq, Preadditive.comp_sum]
    simp_rw [← Category.assoc, ← Functor.map_comp]
    rw [Finset.sum_congr rfl fun y hy => by
      rw [hK a b y.1 y.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 hy)]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [Functor.map_add (ev Y), Preadditive.add_comp, Finset.sum_add_distrib, sum_idO Y a b _ rfl,
      Functor.map_sum, Preadditive.sum_comp]

    simp only [Preadditive.comp_add, Category.comp_id]
    rw [← Category.assoc, ιz_homT Y K a b _ rfl, Preadditive.sum_comp]
    simp_rw [Category.assoc, ιz_d, Preadditive.comp_sum, ← Category.assoc, ← Functor.map_comp]
    rw [Finset.sum_comm (s := antidiagonal (a + b + 1))]
    rw [ιz_dNext Y K a b _ rfl, show ιz Y a b (a + b) ≫ 𝟙 ((tot Y).X (a + b)) = ιz Y a b (a + b) from Category.comp_id _]
    abel

end GlobalTheory.EZ.AWEq

namespace GlobalTheory.EZ

open GlobalTheory.EZ.AWEq

theorem awHomotopyEquiv : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b'), G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → (∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) → (∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') → ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  intro C _ _ _ Y G H K _ hG hH hK
  exact ⟨HomotopyEquiv.mk (awC Y) (shufC Y G hG) (htpyD Y G hG H hH) (htpyT Y G hG K hK), fun _ => rfl⟩

end GlobalTheory.EZ
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialAlexanderWhitneyHomotopyEquivStatement
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b'), G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → (∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) → (∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') → ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  first | (exact @GlobalTheory.EZ.awHomotopyEquiv) | (exact GlobalTheory.EZ.awHomotopyEquiv) | (intros; apply GlobalTheory.EZ.awHomotopyEquiv  <;> assumption)
end
