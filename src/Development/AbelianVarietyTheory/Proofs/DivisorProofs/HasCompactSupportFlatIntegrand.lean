module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsion
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid (k := k)}

theorem isLocallyConstant_of_isTensor {ϖ : kˣ} {e : ℕ} {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) :
    IsLocallyConstant T := by
  classical
  refine (IsLocallyConstant.iff_eventually_eq T).2 fun x => ?_
  have h : ∀ᶠ y in nhds x, ∀ b ∈ γ.toFinset, ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) ∈ 𝒪[k] := by
    refine (Filter.eventually_all_finset _).2 fun b _ => Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun y : G.Args => (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) :=
      continuous_const.mul (((continuous_apply b).matrix_elem i j).sub continuous_const)
    exact (Model.isOpen_int.preimage hc).mem_nhds (by simp)
  filter_upwards [h] with y hy
  rw [← hT.2.2 x (fun b => if b ∈ γ then y b - x b else 0) fun b => ?_]
  · exact hT.1 fun b hb => by simp [show b ∈ γ from hb]
  · split_ifs with hb
    · exact fun i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => hy b (List.mem_toFinset.2 hb) i j)
    · exact zero_mem _

theorem continuous_stepPt {n n' : Type*} {c : ℕ} (x₀ : Matrix n n' k) :
    Continuous fun e : StepVar n c n' → k => stepPt x₀ e := by
  refine continuous_const.add (continuous_matrix fun r s => ?_)
  simp only [of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_fill (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) : Continuous (fill hs x y) := by
  refine continuous_pi ?_
  rintro (⟨i, j⟩ | ⟨i, j⟩) <;> simp only [fill] <;> split_ifs
  · refine Continuous.matrix_transpose (Continuous.matrix_submatrix ?_ _ _)
    unfold downMap
    split_ifs with h
    · exact ((continuous_stepPt _).comp (continuous_apply (⟨j, h⟩ : Fin (G.m - 1)))).matrix_reindex _ _
    · exact continuous_const
    · exact continuous_const
  all_goals exact continuous_const

theorem continuous_phase (x : ColArgs G) : Continuous (phase x) := by
  have hp : ∀ (j : Fin (G.m - 1)) r s, Continuous fun e : Vars G => stepPt (x j) (e j) r s := fun j r s =>
    ((continuous_stepPt _).comp (continuous_apply j)).matrix_elem r s
  refine continuous_finsetSum _ fun j _ => (continuous_finsetSum _ fun i _ => hp j _ _).add ?_
  split_ifs
  · refine continuous_finsetSum _ fun r _ => Continuous.mul ?_ (hp j _ _)
    unfold rowVar
    split_ifs with h
    · refine continuous_finsetSum _ fun l _ => ?_
      split_ifs
      · exact hp ⟨_, h⟩ _ _
      · exact continuous_const
    · exact continuous_const
  · exact continuous_const


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_fill_entry (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) (j : Fin (G.m - 1))
    (rs : StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) :
    ∃ a b c, ∀ e : Vars G, e j rs = fill hs x y e (.theta G.m j) a b - c := by
  refine ⟨frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; have := j.2; omega) rs.1.2,
    frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); have := j.2; omega) rs.1.1,
    basePt _ (x j) rs.1.1 rs.1.2, fun e => ?_⟩
  rw [fill_theta, transpose_apply, downMap, dite_eq_left j.2]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, stepPt, Matrix.add_apply, of_apply]
  rw [dite_eq_left rs.2, add_sub_cancel_left]

theorem exists_isCompact_of_mul_mem {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : GL m k) (B : GL n k) :
    ∃ K : Set (Matrix m n k), IsCompact K ∧ ∀ X, A.val * X * B.val ∈ matLat m (stdLat k n) → X ∈ K := by
  have hO : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have hC : IsCompact (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => (𝒪[k] : Set k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO
  have hc : Continuous fun M : Matrix m n k => (A⁻¹).val * M * (B⁻¹).val :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨_, hC.image hc, fun X hX => ⟨A.val * X * B.val, fun i _ j _ => mem_matLat_stdLat.1 hX i j, ?_⟩⟩
  show (A⁻¹).val * (A.val * X * B.val) * (B⁻¹).val = X
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]

theorem continuous_flatIntegrand (hs : 1 ≤ G.s) {ψ : AddChar k Circle} (hψ : Continuous ψ) {ϖ : kˣ} {e : ℕ}
    {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : Continuous (flatIntegrand hs ψ (moved G keep g T) x y) := by
  have hm : Continuous (G.moveArgs .one g) := continuous_pi fun b =>
    (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
  exact (continuous_const.mul (continuous_const.mul
    ((isLocallyConstant_of_isTensor hT).continuous.comp (hm.comp (continuous_fill hs x y))))).mul
    (continuous_subtype_val.comp (hψ.comp (continuous_phase x).neg))

theorem hasCompactSupport_flatIntegrand (hs : 1 ≤ G.s) (ψ : AddChar k Circle) {ϖ : kˣ} {e : ℕ}
    {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : HasCompactSupport (flatIntegrand hs ψ (moved G keep g T) x y) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  choose a b c h using exists_fill_entry hs x y
  choose K hK hK' using fun j : Fin (G.m - 1) => exists_isCompact_of_mul_mem
    (Assignment.one.read (g (Edge.theta G.m j).tgt))⁻¹ (Assignment.one.read (g (Edge.theta G.m j).src))
  refine HasCompactSupport.intro (K := Set.univ.pi fun j => Set.univ.pi fun rs =>
    (fun M => M (a j rs) (b j rs) - c j rs) '' K j) (isCompact_univ_pi fun j => isCompact_univ_pi fun rs =>
      (hK j).image ((continuous_id.matrix_elem _ _).sub continuous_const)) fun v hv => ?_
  have h0 : T (G.moveArgs .one g (fill hs x y v)) = 0 := by
    by_contra hne
    refine hv fun j _ rs _ => ⟨_, hK' j _ ?_, (h j rs v).symm⟩
    by_contra hn
    exact hne (hT.2.1 _ (.theta G.m j) (by have := j.2; simp [oppositePath]; omega) hn)
  simp [flatIntegrand, moved, Grid.pathAct, h0]

theorem flatIntegrable_of_isTensor [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hψ : Continuous ψ)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) : FlatIntegrable hs ψ ν T := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  intro g x y
  unfold varsVol
  exact (continuous_flatIntegrand hs hψ hT true g x y).integrable_of_hasCompactSupport
    (hasCompactSupport_flatIntegrand hs ψ hT true g x y)

theorem flatIntegrable [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} :
    IsUnif ϖ → Continuous ψ → G.IsTensor ϖ e (oppositePath G.m) T → FlatIntegrable hs ψ ν T :=
  fun _ hψ hT => flatIntegrable_of_isTensor hs ψ ν hψ hT

end GlobalTheory.FunObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model

variable {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D]

def shear (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k :=
  fromRows Y.toRows₁ (Y.toRows₂ + c * Y.toRows₁)

def dil (t : k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k := fromRows Y.toRows₁ (t • Y.toRows₂)

def stack (Y₁ : Matrix R D k) (C : Matrix T R k) : Matrix (R ⊕ T) D k := fromRows Y₁ (C * Y₁)

def shearGL (c : Matrix T R k) : GL (R ⊕ T) k :=
  ⟨fromBlocks 1 cᵀ 0 1, fromBlocks 1 (-cᵀ) 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩

def dilGL (t : kˣ) : GL (R ⊕ T) k :=
  ⟨diagonal (Sum.elim 1 fun _ => (t : k)), diagonal (Sum.elim 1 fun _ => ((t⁻¹ : kˣ) : k)), by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp⟩

@[simp] theorem toRows₁_shear (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : (shear c Y).toRows₁ = Y.toRows₁ := by
  simp [shear]

@[simp] theorem toRows₁_dil (t : k) (Y : Matrix (R ⊕ T) D k) : (dil t Y).toRows₁ = Y.toRows₁ := by
  simp [dil]

@[simp] theorem toRows₁_stack (Y₁ : Matrix R D k) (C : Matrix T R k) : (stack Y₁ C).toRows₁ = Y₁ := by
  simp [stack]

theorem submatrix_inl_eq (Y : Matrix (R ⊕ T) D k) (τ : R → D) :
    Y.submatrix Sum.inl τ = Y.toRows₁.submatrix id τ := rfl

theorem shear_stack (c : Matrix T R k) (Y₁ : Matrix R D k) (C : Matrix T R k) :
    shear c (stack Y₁ C) = stack Y₁ (C + c) := by
  simp [shear, stack, Matrix.add_mul]

theorem dil_stack (t : k) (Y₁ : Matrix R D k) (C : Matrix T R k) :
    dil t (stack Y₁ C) = stack Y₁ (t • C) := by
  simp [dil, stack, smul_mul]

theorem shear_sub_self (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) :
    shear c Y - Y = fromRows 0 (c * Y.toRows₁) := by
  ext (i | i) j <;> simp [shear]

theorem shearGL_transpose_mul (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) :
    (shearGL c).valᵀ * Y = shear c Y := by
  ext (i | i) j <;> simp [shearGL, shear, fromBlocks_transpose, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.one_apply, add_comm]

theorem dilGL_transpose_mul (t : kˣ) (Y : Matrix (R ⊕ T) D k) :
    (dilGL t : GL (R ⊕ T) k).valᵀ * Y = dil (t : k) Y := by
  ext (i | i) j <;> simp [dilGL, dil, diagonal_transpose, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply]

theorem gdet_shearGL (c : Matrix T R k) : gdet (shearGL c) = 1 := by
  ext; simp [shearGL, gdet, det_fromBlocks_zero₂₁]

theorem gdet_dilGL (t : kˣ) : gdet (dilGL t : GL (R ⊕ T) k) = t ^ Fintype.card T := by
  ext; simp [dilGL, gdet, det_diagonal, Fintype.prod_sum_type]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem omB_shearGL (ν : kˣ →* ℂˣ) (c : Matrix T R k) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (shearGL c) 1 Ψ Y = Ψ (shear c Y) := by
  simp [omB, gdet_shearGL, shearGL_transpose_mul]

theorem exists_apow_eq (x : kˣ) (n : ℕ) : ∃ r : ℝ, 0 < r ∧ apow x ((n : ℂ) / 2) = r := by
  refine ⟨GlobalTheory.SplitWeil.nabs k x ^ ((n : ℝ) / 2), Real.rpow_pos_of_pos (nabs_pos x) _, ?_⟩
  rw [apow, Complex.ofReal_cpow (nabs_pos x).le]
  push_cast; rfl

theorem omB_dilGL (ν : kˣ →* ℂˣ) (t : kˣ) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (dilGL t : GL (R ⊕ T) k) 1 Ψ Y =
      (ν t : ℂ) ^ Fintype.card T * apow (t ^ Fintype.card T) ((Fintype.card D : ℂ) / 2) * Ψ (dil (t : k) Y) := by
  simp [omB, gdet_dilGL, dilGL_transpose_mul]

end GlobalTheory.RankChart

namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel

theorem out_mk_sub_mem {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x : H) :
    (((QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H).out : H) : G) - x ∈ L := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  have := L.neg_mem h
  simpa [neg_add_eq_sub] using this

theorem mk_eq_mk_iff {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x y : H) :
    (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H) = QuotientAddGroup.mk y ↔ (x : G) - y ∈ L := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, ← L.neg_mem_iff]
  simp [neg_add_eq_sub]


open scoped Classical in
open Classical in
theorem sum_shift_out {G : Type} [AddCommGroup G] (F : G → ℂ) (H L : AddSubgroup G)
    [Fintype (H ⧸ L.addSubgroupOf H)] (hL : ∀ x y, y - x ∈ L → F y = F x) (hH : ∀ x, F x ≠ 0 → x ∈ H) (x : G) :
    ∑ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
      if x ∈ H then ∑ q : H ⧸ L.addSubgroupOf H, F ((q.out : H) : G) else 0 := by
  split_ifs with hx
  · have key : ∀ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
        F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G) := by
      intro q
      have e : (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q =
          QuotientAddGroup.mk ((⟨x, hx⟩ : H) + q.out) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      rw [e]
      exact (hL (((⟨x, hx⟩ : H) + q.out : H) : G) _ (out_mk_sub_mem H L ((⟨x, hx⟩ : H) + q.out))).symm
    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H))
      (fun q => F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G))
      (fun q => F ((q.out : H) : G)) fun q => rfl
  · refine Finset.sum_eq_zero fun q _ => ?_
    by_contra h
    have := H.sub_mem (hH _ h) (q.out : H).2
    rw [add_sub_cancel_right] at this
    exact hx this


open scoped Classical in
open Classical in
theorem sum_ite_out {G : Type} [AddCommGroup G] (H H' : AddSubgroup G) [Fintype (H' ⧸ H.addSubgroupOf H')]
    (hHH' : H ≤ H') (c : ℂ) (x : G) :
    ∑ q : H' ⧸ H.addSubgroupOf H', (if x + ((q.out : H') : G) ∈ H then c else 0) = if x ∈ H' then c else 0 := by
  split_ifs with hx
  · rw [Finset.sum_eq_single (QuotientAddGroup.mk (⟨-x, H'.neg_mem hx⟩ : H'))]
    · rw [if_pos]
      have := out_mk_sub_mem H' H (⟨-x, H'.neg_mem hx⟩ : H')
      rwa [sub_neg_eq_add, add_comm] at this
    · intro q _ hq
      rw [if_neg]
      intro hmem
      apply hq
      rw [← QuotientAddGroup.out_eq' q, mk_eq_mk_iff]
      rwa [sub_neg_eq_add, add_comm]
    · simp
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hmem
    have := H'.sub_mem (hHH' hmem) (q.out : H').2
    rw [add_sub_cancel_right] at this
    exact hx this

end GlobalTheory.RankChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRows
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRows
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

def rowRenum (e : A ≃ A') : Matrix A D k ≃ₜ Matrix A' D k where
  toFun Y := Y.submatrix e.symm id
  invFun Y' := Y'.submatrix e id
  left_inv Y := by ext i j; simp
  right_inv Y' := by ext i j; simp
  continuous_toFun := continuous_id.matrix_submatrix _ _
  continuous_invFun := continuous_id.matrix_submatrix _ _

theorem comp_rowRenum_mem_SB (e : A ≃ A') {f : Matrix A' D k → ℂ} (hf : f ∈ SB (Matrix A' D k)) :
    (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k) :=
  ⟨hf.1.comp_continuous (rowRenum (k := k) (D := D) e).continuous,
    hf.2.comp_homeomorph (rowRenum (k := k) (D := D) e)⟩

def glRenum (e : A ≃ A') : GL A' k →* GL A k :=
  Units.map (Matrix.reindexAlgEquiv k k e.symm).toMonoidHom

theorem glRenum_val (e : A ≃ A') (g : GL A' k) : (glRenum e g).val = g.val.submatrix e e := rfl

theorem gdet_glRenum (e : A ≃ A') (g : GL A' k) :
    GlobalTheory.SplitFlip.gdet (glRenum e g) = GlobalTheory.SplitFlip.gdet g := by
  ext
  simp [GlobalTheory.SplitFlip.gdet, glRenum_val, Matrix.det_submatrix_equiv_self]

theorem omB_comp_rowRenum (ν : kˣ →* ℂˣ) (e : A ≃ A') (g : GL A' k) (Ψ : Matrix A' D k → ℂ) :
    (fun Y : Matrix A D k => GlobalTheory.SplitFlip.omB ν ν g 1 Ψ (Y.submatrix e.symm id)) =
      GlobalTheory.SplitFlip.omB ν ν (glRenum e g) 1 (fun Y : Matrix A D k => Ψ (Y.submatrix e.symm id)) := by
  funext Y
  simp only [GlobalTheory.SplitFlip.omB, gdet_glRenum, Units.val_one, Matrix.mul_one]
  congr 1
  · simp
  · congr 1
    rw [glRenum_val]
    have hY : Y = (Y.submatrix e.symm id).submatrix e id := by ext; simp
    conv_rhs => rw [hY]
    rw [show (g.val.submatrix e e)ᵀ = (g.valᵀ).submatrix e e from rfl, Matrix.submatrix_mul_equiv]
    ext; simp

theorem rowRenum_SB_Nsp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (ν : kˣ →* ℂˣ) (e : A ≃ A'),
    (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧
    (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν,
      (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ ν e
  refine ⟨fun f hf => comp_rowRenum_mem_SB e hf, ?_⟩
  let L : (Matrix A' D k → ℂ) →ₗ[ℂ] (Matrix A D k → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun Y : Matrix A D k => Y.submatrix e.symm id)
  have hle : Nsp k A' D ν ≤ (Nsp k A D ν).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, Ψ', hΨ', rfl⟩
    show L (GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ') ∈ Nsp k A D ν
    rw [map_sub]
    have h1 : L (GlobalTheory.SplitFlip.omB ν ν g 1 Ψ') =
        GlobalTheory.SplitFlip.omB ν ν (glRenum e g) 1 (fun Y : Matrix A D k => Ψ' (Y.submatrix e.symm id)) :=
      omB_comp_rowRenum ν e g Ψ'
    rw [h1]
    exact sub_mem_Nsp ν (glRenum e g) (comp_rowRenum_mem_SB e hΨ')
  intro f hf
  exact hle hf

end GlobalTheory.RankStrata
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRowsStatement
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_reindex_rows : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) (e : A ≃ A'), (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧ (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν, (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by
  first | exact @GlobalTheory.RankStrata.rowRenum_SB_Nsp | exact GlobalTheory.RankStrata.rowRenum_SB_Nsp | (intros; apply GlobalTheory.RankStrata.rowRenum_SB_Nsp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
open GlobalTheory.WeilM Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.CoverSB

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) {g : X → ℂ}
    (hg : g ∈ SB X) : W.indicator g ∈ SB X := by
  classical
  refine ⟨?_, hg.2.mono fun x hx => by
    by_contra h; exact hx (by by_cases hxW : x ∈ W <;> simp [Set.indicator, hxW, Function.notMem_support.1 h])⟩
  have h1 : IsLocallyConstant (W.indicator (fun _ => (1 : ℂ))) :=
    (IsLocallyConstant.iff_isOpen_fiber).2 fun c => by
      by_cases h0 : c = 1 <;> by_cases h0' : c = 0
      · subst h0; simp at h0'
      · subst h0
        convert hW.isOpen using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
      · subst h0'
        convert hW.compl.isOpen using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
      · convert (isOpen_empty : IsOpen (∅ : Set X)) using 1
        ext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx, Ne.symm h0, Ne.symm h0']
  have e : W.indicator g = fun x => W.indicator (fun _ => (1 : ℂ)) x * g x := by
    funext x; by_cases hx : x ∈ W <;> simp [Set.indicator, hx]
  rw [e]
  exact h1.mul hg.1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isClopen_subset {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    {U : Set (Matrix A D k)} (hU : IsOpen U) {x : Matrix A D k} (hx : x ∈ U) :
    ∃ V : Set (Matrix A D k), IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  have h0 : (fun y => x + y) ⁻¹' U ∈ 𝓝 (0 : Matrix A D k) := by
    refine (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using hU.mem_nhds hx
  obtain ⟨a, ha⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset h0
  have hBo := GlobalTheory.LocMod.Inhab.isOpen_box (Y := A) (Y' := D) a
  have hBc : IsClosed ((GlobalTheory.LocMod.Inhab.box A D a : AddSubgroup (Matrix A D k)) : Set (Matrix A D k)) :=
    AddSubgroup.isClosed_of_isOpen _ hBo
  refine ⟨(fun y => y - x) ⁻¹' (GlobalTheory.LocMod.Inhab.box A D a : Set (Matrix A D k)),
    ⟨hBc.preimage (continuous_id.sub continuous_const), hBo.preimage (continuous_id.sub continuous_const)⟩,
    by simpa using (GlobalTheory.LocMod.Inhab.box A D a).zero_mem, fun y hy => ?_⟩
  have := ha _ hy
  simpa using this

end GlobalTheory.CoverSB

namespace GlobalTheory.CoverSB

theorem mem_span_of_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ι : Type) [Finite ι] (U : ι → Set (Matrix A D k)), (∀ i, IsOpen (U i)) → ∀ f ∈ SB (Matrix A D k), (∀ Y, f Y ≠ 0 → ∃ i, Y ∈ U i) → f ∈ Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} := by
  intro k _ _ _ _ A D _ _ _ _ ι _ U hU f hf hcov
  set P := Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} with hP

  have hcl : IsClosed (Function.support f) := by
    have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hf.1.isOpen_fiber 0).isClosed_compl
  have hcpt : IsCompact (Function.support f) := by
    have := hf.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at this
    exact this
  let p : Set (Matrix A D k) → Prop := fun T => ∃ W, IsClopen W ∧ T ⊆ W ∧
    ∀ g ∈ SB (Matrix A D k), Function.support g ⊆ W → g ∈ P
  have hp : p (Function.support f) := by
    refine hcpt.induction_on ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, subset_rfl, fun g _ hg => ?_⟩
      have : g = 0 := by
        funext y; by_contra h; exact hg h
      rw [this]; exact P.zero_mem
    · rintro s t hst ⟨W, hW, htW, h⟩
      exact ⟨W, hW, hst.trans htW, h⟩
    · rintro s t ⟨W₁, hW₁, hs, h₁⟩ ⟨W₂, hW₂, ht, h₂⟩
      refine ⟨W₁ ∪ W₂, hW₁.union hW₂, Set.union_subset_union hs ht, fun g hg hsupp => ?_⟩
      rw [← Set.indicator_self_add_compl W₁ g]
      refine P.add_mem (h₁ _ (indicator_mem_SB hW₁ hg) Set.support_indicator_subset)
        (h₂ _ (indicator_mem_SB hW₁.compl hg) fun y hy => ?_)
      have hyc : y ∈ W₁ᶜ := Set.support_indicator_subset hy
      have hyg : y ∈ Function.support g := by
        by_contra h; exact hy (by simp [Set.indicator, hyc, Function.notMem_support.1 h])
      rcases hsupp hyg with h | h
      · exact absurd h hyc
      · exact h
    · intro x hx
      obtain ⟨i, hi⟩ := hcov x hx
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isClopen_subset (hU i) hi
      refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.isOpen.mem_nhds hxV), V, hV, subset_rfl, fun g hg hsupp => ?_⟩
      exact Submodule.subset_span ⟨hg, i, fun Y hY => hVU (hsupp hY)⟩
  obtain ⟨W, -, hW, h⟩ := hp
  exact h f hf hW

end GlobalTheory.CoverSB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnityStatement
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_partition_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ι : Type) [Finite ι] (U : ι → Set (Matrix A D k)), (∀ i, IsOpen (U i)) → ∀ f ∈ SB (Matrix A D k), (∀ Y, f Y ≠ 0 → ∃ i, Y ∈ U i) → f ∈ Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} := by
  first | exact @GlobalTheory.CoverSB.mem_span_of_cover | exact GlobalTheory.CoverSB.mem_span_of_cover | (intros; apply GlobalTheory.CoverSB.mem_span_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
noncomputable section

open Coalgebra Bialgebra WithConv

namespace GlobalTheory

namespace PDiv

variable {R A C D : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing D]
  [Bialgebra R A] [Bialgebra R C] [Bialgebra R D]

theorem cotMap_surjective {f : C →ₐc[R] A} (hf : Function.Surjective f) :
    Function.Surjective (cotMap f) :=
  AugCot.map_surjective _ _ hf

theorem dUnit_mem_range_of_mem_kerIdeal (g : D →ₐc[R] C) {c : C} (hc : c ∈ kerIdeal g) :
    dUnit (R := R) c ∈ LinearMap.range (cotMap g) := by
  suffices h : counitAlgHom R C c = 0 ∧ dUnit (R := R) c ∈ LinearMap.range (cotMap g) from h.2
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨?_, dUnit (R := R) a, cotMap_d g a⟩
    have ha' : counit (R := R) a = 0 := ha
    simpa using ha'
  | zero => exact ⟨map_zero _, by rw [dUnit, map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    exact ⟨by rw [map_add (f := _), hx.1, hy.1, add_zero], by rw [dUnit, map_add (f := _)]; exact add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    refine ⟨by rw [smul_eq_mul, map_mul, hx.1, mul_zero], ?_⟩
    rw [smul_eq_mul, dUnit, AugCot.d_mul, hx.1, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ hx.2

theorem exact_cotMap {f : C →ₐc[R] A} (hf : Function.Surjective f) (g : D →ₐc[R] C)
    (hk : RingHom.ker f = kerIdeal g) : Function.Exact (cotMap g) (cotMap f) := by
  intro w
  constructor
  · intro hw
    obtain ⟨x, rfl⟩ := (AugCot.exact_kerMap_map (f : C →ₐ[R] A)
      (BialgHomClass.counitAlgHom_comp f) hf w).1 hw
    obtain ⟨v, hv⟩ := dUnit_mem_range_of_mem_kerIdeal g (hk.le x.2)
    exact ⟨v, hv.trans (AugCot.kerMap_apply _ _ x).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨a, rfl⟩ := AugCot.d_surjective _ v
    rw [cotMap_d, cotMap_d]
    have h := (kerIdeal_le_ker_iff g (f : C →ₐ[R] A)).1 hk.ge a
    exact (congrArg (dUnit (R := R)) h).trans (AugCot.d_algebraMap _ _)

theorem cotMap_mulBy [IsCocomm R C] (m : ℕ) (w : Cot (R := R) (A := C)) :
    cotMap (mulBy (R := R) (A := C) m) w = (m : R) • w := by
  rw [mulBy, cotMap_pow, ofConv_toConv, cotMap_id, Nat.cast_smul_eq_nsmul]
  rfl

theorem cotMap_eq_zero_iff [IsCocomm R C] {f : C →ₐc[R] A} (hf : Function.Surjective f) {m : ℕ}
    (hk : RingHom.ker f = torsionIdeal (R := R) (A := C) m) (w : Cot (R := R) (A := C)) :
    cotMap f w = 0 ↔ ∃ v : Cot (R := R) (A := C), w = (m : R) • v := by
  rw [exact_cotMap hf _ hk w]
  exact exists_congr fun v => by rw [cotMap_mulBy, eq_comm]

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)

theorem cotMap_res_surjective (n : ℕ) : Function.Surjective (cotMap (G.res n)) :=
  cotMap_surjective (G.res_surjective n)

theorem cotMap_res_eq_zero_iff (n : ℕ) (w : Cot (R := O) (A := G.A (n + 1))) :
    cotMap (G.res n) w = 0 ↔ ∃ v, w = (p : O) ^ n • v := by
  rw [cotMap_eq_zero_iff (G.res_surjective n) (G.ker_res n), Nat.cast_pow]

def omegaLevel (n : ℕ) : G.omega →ₗ[O] Cot (R := O) (A := G.A n) :=
  LinearMap.proj n ∘ₗ G.omegaSub.subtype

@[simp] theorem omegaLevel_apply (n : ℕ) (w : G.omega) : G.omegaLevel n w = w.1 n := rfl

@[simp] theorem cotMap_res_omega (n : ℕ) (w : G.omega) :
    cotMap (G.res n) (w.1 (n + 1)) = w.1 n := w.2 n

theorem omega_val_eq_zero_of_le {m n : ℕ} (h : m ≤ n) {w : G.omega} (hw : w.1 n = 0) :
    w.1 m = 0 := by
  induction n, h using Nat.le_induction with
  | base => exact hw
  | succ n _ ih => exact ih (by rw [← w.2 n, hw, map_zero])

theorem cot_zero_eq_zero (w : Cot (R := O) (A := G.A 0)) : w = 0 := by
  simpa using G.pow_smul_cot 0 w

theorem omegaLevel_surjective (n : ℕ) : Function.Surjective (G.omegaLevel n) := by
  have hsec := fun k => (G.cotMap_res_surjective k).hasRightInverse
  choose s hs using hsec

  have key : ∀ (n : ℕ) (x : Cot (R := O) (A := G.A (n + 1))), cotMap (G.res n) x = 0 →
      ∃ w : G.omega, w.1 (n + 1) = x := by
    intro n x hx
    let u : ∀ k, Cot (R := O) (A := G.A k) := fun k =>
      if h : n + 1 ≤ k then Nat.leRecOn h (fun {k} => s k) x else 0
    refine ⟨⟨u, fun k => ?_⟩, by simp [u, Nat.leRecOn_self]⟩
    rcases lt_trichotomy k n with hk | rfl | hk
    · simp only [u]
      rw [dite_eq_right (by omega), dite_eq_right (by omega), map_zero]
    · simp only [u]
      rw [dite_eq_left le_rfl, dite_eq_right (by omega), Nat.leRecOn_self, hx]
    · simp only [u]
      rw [dite_eq_left (by omega), dite_eq_left (show n + 1 ≤ k from hk), Nat.leRecOn_succ (show n + 1 ≤ k from hk)]
      exact hs k _
  induction n with
  | zero => exact fun x => ⟨0, (G.cot_zero_eq_zero _).trans (G.cot_zero_eq_zero _).symm⟩
  | succ n ih =>
    intro x
    obtain ⟨v, hv⟩ := ih (cotMap (G.res n) x)
    obtain ⟨w, hw⟩ := key n (x - v.1 (n + 1)) (by rw [map_sub, v.2 n, ← hv]; exact sub_self _)
    refine ⟨w + v, ?_⟩
    rw [map_add (f := _), omegaLevel_apply, omegaLevel_apply, hw, sub_add_cancel]

theorem exists_sub_pow_smul_val_succ (n : ℕ) (w : G.omega) (hw : w.1 n = 0) :
    ∃ v : G.omega, (w - (p : O) ^ n • v).1 (n + 1) = 0 := by
  obtain ⟨x, hx⟩ := (G.cotMap_res_eq_zero_iff n (w.1 (n + 1))).1 ((w.2 n).trans hw)
  obtain ⟨v, rfl⟩ := G.omegaLevel_surjective (n + 1) x
  refine ⟨v, ?_⟩
  change w.1 (n + 1) - (p : O) ^ n • v.1 (n + 1) = 0
  rw [hx, omegaLevel_apply, sub_self]

theorem omega_val_eq_zero_iff (n : ℕ) (w : G.omega) :
    w.1 n = 0 ↔ ∃ v : G.omega, w = (p : O) ^ n • v := by
  refine ⟨fun hw => ?_, ?_⟩
  swap
  · rintro ⟨v, rfl⟩
    exact G.pow_smul_cot n (v.1 n)
  choose! c hc using G.exists_sub_pow_smul_val_succ
  let r : ℕ → G.omega := fun j => Nat.rec w (fun j x => x - (p : O) ^ (n + j) • c (n + j) x) j
  have hr : ∀ j, (r j).1 (n + j) = 0 := fun j => by
    induction j with
    | zero => exact hw
    | succ j ih => exact hc _ _ ih
  let t : ℕ → G.omega := fun k => ∑ j ∈ Finset.range k, (p : O) ^ j • c (n + j) (r j)
  have ht : ∀ k, w = r k + (p : O) ^ n • t k := fun k => by
    induction k with
    | zero => simp [t, r]
    | succ k ih =>
      have h1 : r (k + 1) = r k - (p : O) ^ (n + k) • c (n + k) (r k) := rfl
      have h2 : t (k + 1) = t k + (p : O) ^ k • c (n + k) (r k) := Finset.sum_range_succ _ _
      rw [h1, h2, smul_add, smul_smul, ← pow_add]
      exact ih.trans (by abel)
  refine ⟨⟨fun k => (t k).1 k, fun k => ?_⟩, Subtype.ext (funext fun k => ?_)⟩
  · have h2 : t (k + 1) = t k + (p : O) ^ k • c (n + k) (r k) := Finset.sum_range_succ _ _
    rw [(t (k + 1)).2 k, h2]
    change (t k).1 k + (p : O) ^ k • (c (n + k) (r k)).1 k = _
    rw [pow_smul_cot, add_zero]
  · have h := congrArg (fun x : G.omega => x.1 k) (ht k)
    refine h.trans ?_
    change (r k).1 k + (p : O) ^ n • (t k).1 k = (p : O) ^ n • (t k).1 k
    rw [G.omega_val_eq_zero_of_le (Nat.le_add_left k n) (hr k), zero_add]

theorem ker_omegaLevel (n : ℕ) :
    LinearMap.ker (G.omegaLevel n) = Ideal.span {(p : O)} ^ n • (⊤ : Submodule O G.omega) := by
  ext w
  rw [LinearMap.mem_ker, omegaLevel_apply, omega_val_eq_zero_iff, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact exists_congr fun v => by simp [eq_comm]

def omegaQuotEquiv (n : ℕ) :
    (G.omega ⧸ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.omega)) ≃ₗ[O] Cot (R := O) (A := G.A n) :=
  Submodule.quotEquivOfEq _ _ (G.ker_omegaLevel n).symm ≪≫ₗ
    (G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)

@[simp] theorem omegaQuotEquiv_mk (n : ℕ) (w : G.omega) :
    G.omegaQuotEquiv n (Submodule.Quotient.mk w) = w.1 n := rfl

theorem omega_smodEq_iff (n : ℕ) (v w : G.omega) :
    v ≡ w [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.omega)] ↔ v.1 n = w.1 n := by
  rw [SModEq.sub_mem, ← ker_omegaLevel, LinearMap.mem_ker, map_sub, sub_eq_zero]
  rfl

instance isAdicComplete_omega : IsAdicComplete (Ideal.span {(p : O)}) G.omega where
  haus' w hw := Subtype.ext (funext fun n => (G.omega_smodEq_iff n w 0).1 (hw n))
  prec' f hf := by
    refine ⟨⟨fun k => (f k).1 k, fun k => ?_⟩, fun n => (G.omega_smodEq_iff n _ _).2 rfl⟩
    rw [(f (k + 1)).2 k]
    exact ((G.omega_smodEq_iff k _ _).1 (hf (Nat.le_succ k))).symm

end PDivGroup

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicProperties
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section
namespace GlobalTheory.KSp

section PairAlg

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem pr_eq_trace (Q : Matrix α α E) (x y : Matrix α ν E) :
    pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  have h : fromCols x (0 : Matrix α ν E) * stdJ ν E * ((fromCols (0 : Matrix α ν E) y).map c)ᵀ = x * (y.map c)ᵀ := by
    ext i k
    simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [pr, form, hTens_eq, h]
  congr 2
  simp only [Matrix.trace, diag, Matrix.mul_apply, transpose_apply]
  rw [Finset.sum_comm]

theorem trace_single_pair (Q : Matrix α α E) (y : Matrix α ν E) (i : α) (j : ν) (z : E) :
    Matrix.trace (Qᵀ * (Matrix.single i j z * (y.map c)ᵀ)) = z * (Q * y.map c) i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Finset.mul_sum, ite_and]
  refine Finset.sum_congr rfl fun _ _ => by ring

def prLin (Q : Matrix α α E) : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))))
    (fun x x' y => by simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])
    (fun x y y' => by
      rw [show (y + y').map c = y.map c + y'.map c from Matrix.map_add _ (map_add c) _ _]
      simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by
      rw [show (t • y).map c = t • y.map c from by ext i j; simp [map_smul]]
      simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])

end PairAlg

end GlobalTheory.KSp

namespace GlobalTheory.KSp

theorem pr_alg : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν]
    (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F,
      (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧
      (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧
      ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q hQ
  have hc : ∀ z, c (c z) = z := hE.invol
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  have hap : ∀ x y : Matrix α ν E, prLin c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) :=
    fun _ _ => rfl
  refine ⟨prLin c Q, fun x y => by rw [hap, pr_eq_trace], fun x y => ?_, fun y hy => ?_, fun x y a => ?_, hap⟩
  ·
    have h : Matrix.trace (Qᵀ * (y * (x.map c)ᵀ)) = c (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.trace, diag, Matrix.mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc, hQ.1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [hap, hap, h, ht]
  ·
    obtain ⟨bE, -, -⟩ := hE.basis
    haveI : Module.Finite F E := Module.Finite.of_basis bE
    have htr : Algebra.trace F E 1 ≠ 0 := by
      rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hw : Q * y.map c = 0 := by
      ext i j
      by_contra hij
      apply htr
      have := hy (Matrix.single i j ((Q * y.map c) i j)⁻¹)
      rw [hap, trace_single_pair, inv_mul_cancel₀ hij] at this
      simpa using this
    have hy0 : y.map c = 0 := by
      have := congrArg (fun m => Q⁻¹ * m) hw
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ.2] using this
    ext i j
    exact c.toRingHom.injective (by simpa using congrFun (congrFun hy0 i) j)
  ·
    have h : ((y * (a.map c)ᵀ).map c)ᵀ = a * (y.map c)ᵀ := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mul_apply, map_sum, hc, mul_comm]
    rw [hap, hap, h, Matrix.mul_assoc]

end GlobalTheory.KSp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicPropertiesStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F, (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧ (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧ ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  first | exact @GlobalTheory.KSp.pr_alg | exact GlobalTheory.KSp.pr_alg | (intros; apply GlobalTheory.KSp.pr_alg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffEl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffEl
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredElements

theorem preservesFilteredColimits_modules_iff_elements :
    ∀ (Λ : Type 1) [Ring Λ] (N : CommRingCat.{0} ⥤ ModuleCat.{1} Λ), (PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})) ∧ (PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, (N.map (c.ι.app j)).hom y = x) ∧ ∀ j (y : N.obj (D.obj j)), (N.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (N.map (D.map f)).hom y = 0) := by
  intro Λ _ N
  have hP : PreservesColimitsOfSize.{0, 0} (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 1, 0, 0} Λ
  have h1 : PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) := by
    constructor
    · intro h
      exact comp_preservesFilteredColimits N (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})
    · intro h
      constructor
      intro J _ _
      have hR : ReflectsColimitsOfShape J (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1}) :=
        ModuleCat.reflectsColimitsOfShape.{1, 1, 0, 0} Λ J
      constructor
      intro K
      exact preservesColimit_of_reflects_of_preserves N (forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})
  refine ⟨h1, ?_⟩
  rw [h1, GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements]
  rfl

end GlobalTheory.EtC.FilteredElements
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffElStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements : ∀ (Λ : Type 1) [Ring Λ] (N : CommRingCat.{0} ⥤ ModuleCat.{1} Λ), (PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})) ∧ (PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, (N.map (c.ι.app j)).hom y = x) ∧ ∀ j (y : N.obj (D.obj j)), (N.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (N.map (D.map f)).hom y = 0) := by
  first | (exact @GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements) | (exact GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements) | (intros; apply GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModularFormLevelOneOfInvariantQExpansion
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ : ∀ (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (a : ℕ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) → _root_.GlobalTheory.QFam.HasQ N f a → _root_.ReciprocityTheory.ChartRestriction.L1.IsMF k f := by
  intro N k f a hN hinv h
  refine ⟨{ toFun := f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ },
    fun _ => rfl⟩
  · rintro _ ⟨γ, rfl⟩
    exact (ModularForm.SL_slash f γ).symm.trans (hinv γ)
  · exact h.mdifferentiable hN
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [hinv γ]
    exact (_root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN h).2

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideMore
theorem GlobalTheory.FourClauses.adm : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun h k _ _ _ _ n V _ _ π hs hi => (h k).1 (Fin n) V π hs hi
end
