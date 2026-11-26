module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForWeylElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeGen

open Matrix GlobalTheory.SympChange

variable {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]

def upM (T : Matrix κ κ K) : Matrix (κ ⊕ κ) (κ ⊕ κ) K := fromBlocks 1 T 0 1

theorem weylM_mem : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inr rfl)

theorem leviM_mem (A : Matrix κ κ K) (h : IsUnit A.det) :
    leviM A ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inl ⟨A, h, rfl⟩))

theorem unipM_mem (S : Matrix κ κ K) (h : Sᵀ = S) :
    unipM S ∈ Submonoid.closure (gens (F := K) (κ := κ)) :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨S, h, rfl⟩))

theorem upM_eq (T : Matrix κ κ K) :
    upM T = weylM * unipM (-T) * (weylM * weylM * weylM) := by
  simp [upM, weylM, unipM, fromBlocks_multiply]

theorem upM_mem (T : Matrix κ κ K) (h : Tᵀ = T) :
    upM T ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  rw [upM_eq]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem (unipM_mem _ (by rw [transpose_neg, h])))
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ weylM_mem weylM_mem) weylM_mem)

theorem isSymp_mul {G H : Matrix (κ ⊕ κ) (κ ⊕ κ) K} (hG : IsSymp G) (hH : IsSymp H) :
    IsSymp (G * H) := by
  unfold IsSymp at *
  calc (G * H)ᵀ * weylM * (G * H) = Hᵀ * (Gᵀ * weylM * G) * H := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = weylM := by rw [hG, hH]

theorem isSymp_upM (T : Matrix κ κ K) (h : Tᵀ = T) : IsSymp (upM T) := by
  simp [IsSymp, upM, weylM, fromBlocks_transpose, fromBlocks_multiply, h]

theorem weyl_sq : (weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * weylM = -1 := by
  simp [weylM, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem exists_sym_isUnit (a c : Matrix κ κ K) (hs : aᵀ * c = cᵀ * a)
    (hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0) :
    ∃ T : Matrix κ κ K, Tᵀ = T ∧ IsUnit (a + T * c).det := by
  classical
  let P : Finset κ → Prop := fun s => ∀ y, (∀ i ∉ s, (a *ᵥ y) i = 0) → a *ᵥ y = 0
  have hP0 : P ∅ := fun y hy => funext fun i => hy i (Finset.notMem_empty i)
  obtain ⟨s, hs_mem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, hP0⟩⟩
  have hsP : P s := (Finset.mem_filter.1 hs_mem).2
  have key : ∀ z : κ → K, (∀ i ∈ s, z i = 0) → (∀ y, z ⬝ᵥ (a *ᵥ y) = 0) → z = 0 := by
    intro z hzs hzo
    funext j
    by_cases hj : j ∈ s
    · exact hzs j hj
    · have hnot : ¬ P (insert j s) := by
        intro hP'
        have := hmax (insert j s) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP'⟩)
        rw [Finset.card_insert_of_notMem hj] at this
        omega
      simp only [P, not_forall] at hnot
      obtain ⟨y, hy, hne⟩ := hnot
      have hvj : (a *ᵥ y) j ≠ 0 := by
        intro h0
        apply hne
        apply hsP y
        intro i hi
        by_cases hij : i = j
        · rw [hij]; exact h0
        · exact hy i (by simp [hij, hi])
      have hsum : z ⬝ᵥ (a *ᵥ y) = z j * (a *ᵥ y) j := by
        unfold dotProduct
        apply Finset.sum_eq_single j
        · intro i _ hij
          by_cases his : i ∈ s
          · rw [hzs i his, zero_mul]
          · rw [hy i (by simp [hij, his]), mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have h0 := hzo y
      rw [hsum] at h0
      exact (mul_eq_zero.1 h0).resolve_right hvj
  set T : Matrix κ κ K := diagonal fun i => if i ∈ s then 1 else 0 with hTdef
  have hTe : ∀ w : κ → K, ∀ i, (T *ᵥ w) i = (if i ∈ s then 1 else 0) * w i := fun w i => by
    simp [hTdef, mulVec_diagonal]
  have hx : ∀ x, (a + T * c) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [add_mulVec, ← mulVec_mulVec] at hx
    have hx2 : ∀ i, (a *ᵥ x) i + (if i ∈ s then 1 else 0) * (c *ᵥ x) i = 0 := fun i => by
      rw [← hTe]; exact congrFun hx i
    have hax : a *ᵥ x = 0 := hsP x (fun i hi => by
      have := hx2 i
      rwa [if_neg hi, zero_mul, add_zero] at this)
    have hcs : ∀ i ∈ s, (c *ᵥ x) i = 0 := fun i hi => by
      have := hx2 i
      rwa [if_pos hi, one_mul, hax, Pi.zero_apply, zero_add] at this
    have horth : ∀ y, (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = 0 := fun y => by
      calc (c *ᵥ x) ⬝ᵥ (a *ᵥ y) = x ⬝ᵥ ((cᵀ * a) *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x cᵀ, vecMul_transpose]
        _ = x ⬝ᵥ ((aᵀ * c) *ᵥ y) := by rw [hs]
        _ = (a *ᵥ x) ⬝ᵥ (c *ᵥ y) := by
            rw [← mulVec_mulVec, dotProduct_mulVec x aᵀ, vecMul_transpose]
        _ = 0 := by rw [hax, zero_dotProduct]
    exact hinj x hax (key _ hcs horth)
  refine ⟨T, by simp [hTdef], isUnit_iff_ne_zero.2 fun hdet => ?_⟩
  obtain ⟨v, hv, hmv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  exact hv (hx v hmv)

theorem symp_blocks {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) :
    aᵀ * c = cᵀ * a ∧ aᵀ * d = 1 + cᵀ * b ∧ bᵀ * d = dᵀ * b := by
  simp only [IsSymp, weylM, fromBlocks_transpose, fromBlocks_multiply] at h
  obtain ⟨h11, h12, -, h22⟩ := fromBlocks_inj.1 h
  simp at h11 h12 h22
  refine ⟨(neg_add_eq_zero.1 h11).symm, ?_, (neg_add_eq_zero.1 h22).symm⟩
  rw [← h12]; abel

theorem mem_of_isUnit {a b c d : Matrix κ κ K} (h : IsSymp (fromBlocks a b c d)) (ha : IsUnit a.det) :
    fromBlocks a b c d ∈ Submonoid.closure (gens (F := K) (κ := κ)) := by
  obtain ⟨e1, e2, e3⟩ := symp_blocks h
  have haa : a * a⁻¹ = 1 := mul_nonsing_inv a ha
  have hai : a⁻¹ * a = 1 := nonsing_inv_mul a ha
  have hT1 : a⁻¹ᵀ * aᵀ = 1 := by rw [← transpose_mul, haa, transpose_one]
  have hT2 : aᵀ * a⁻¹ᵀ = 1 := by rw [← transpose_mul, hai, transpose_one]
  set Y := c * a⁻¹ with hYdef
  have hY : Yᵀ = Y := by
    rw [hYdef, transpose_mul]
    calc a⁻¹ᵀ * cᵀ = a⁻¹ᵀ * cᵀ * (a * a⁻¹) := by rw [haa, Matrix.mul_one]
      _ = a⁻¹ᵀ * (cᵀ * a) * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ᵀ * (aᵀ * c) * a⁻¹ := by rw [e1]
      _ = (a⁻¹ᵀ * aᵀ) * c * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = c * a⁻¹ := by rw [hT1, Matrix.one_mul]
  have hd : d = a⁻¹ᵀ + Y * b := by
    calc d = (a⁻¹ᵀ * aᵀ) * d := by rw [hT1, Matrix.one_mul]
      _ = a⁻¹ᵀ * (aᵀ * d) := by rw [Matrix.mul_assoc]
      _ = a⁻¹ᵀ + (a⁻¹ᵀ * cᵀ) * b := by rw [e2, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
      _ = a⁻¹ᵀ + Y * b := by rw [← transpose_mul, ← hYdef, hY]
  set X := a⁻¹ * b with hXdef
  have hX : Xᵀ = X := by
    have e3' := e3
    rw [hd, Matrix.mul_add, transpose_add, Matrix.add_mul, transpose_mul, hY, transpose_transpose] at e3'
    simp only [← Matrix.mul_assoc] at e3'
    rw [hXdef, transpose_mul]
    exact add_right_cancel e3'
  have hG : fromBlocks a b c d = unipM Y * leviM a * upM X := by
    simp only [unipM, leviM, upM, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
    congr 1
    · rw [hXdef, ← Matrix.mul_assoc, haa, Matrix.one_mul]
    · rw [hYdef, Matrix.mul_assoc, hai, Matrix.mul_one]
    · rw [hd, hXdef, hYdef, add_comm]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc a a⁻¹ b, haa, Matrix.one_mul]
  rw [hG]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (unipM_mem _ hY) (leviM_mem _ ha)) (upM_mem _ hX)

theorem mem_closure_gens : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  intro K _ _ κ _ _ G hG
  rw [← fromBlocks_toBlocks G] at hG ⊢
  set a := G.toBlocks₁₁
  set b := G.toBlocks₁₂
  set c := G.toBlocks₂₁
  set d := G.toBlocks₂₂
  obtain ⟨e1, -, -⟩ := symp_blocks hG

  have hL : (-(weylM * (fromBlocks a b c d)ᵀ * weylM)) * fromBlocks a b c d = 1 := by
    have h := hG
    unfold IsSymp at h
    have e : weylM * (fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d
        = weylM * ((fromBlocks a b c d)ᵀ * weylM * fromBlocks a b c d) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, e, h, weyl_sq, neg_neg]
  have hinj : ∀ x, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0 := by
    intro x hax hcx
    have hv : fromBlocks a b c d *ᵥ Sum.elim x 0 = 0 := by
      rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, hax, hcx, mulVec_zero, mulVec_zero]
      simp
    have h0 : Sum.elim x (0 : κ → K) = 0 := by
      rw [← Matrix.one_mulVec (Sum.elim x 0), ← hL, ← mulVec_mulVec, hv, mulVec_zero]
    funext i
    exact congrFun h0 (Sum.inl i)
  obtain ⟨T, hT, hu⟩ := exists_sym_isUnit a c e1 hinj
  have hH : upM T * fromBlocks a b c d = fromBlocks (a + T * c) (b + T * d) c d := by
    simp [upM, fromBlocks_multiply]
  have hHs : IsSymp (fromBlocks (a + T * c) (b + T * d) c d) := hH ▸ isSymp_mul (isSymp_upM T hT) hG
  have hinv : upM (-T) * upM T = (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) := by
    simp [upM, fromBlocks_multiply]
  have : fromBlocks a b c d = upM (-T) * fromBlocks (a + T * c) (b + T * d) c d := by
    rw [← hH, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [this]
  exact Submonoid.mul_mem _ (upM_mem _ (by rw [transpose_neg, hT])) (mem_of_isUnit hHs hu)

end GlobalTheory.SympChangeGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementaryStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_group_generated_by_elementary : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  first | exact @GlobalTheory.SympChangeGen.mem_closure_gens | exact GlobalTheory.SympChangeGen.mem_closure_gens | (intros; apply GlobalTheory.SympChangeGen.mem_closure_gens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompare
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

theorem sumElim_weylM_map {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
    [Algebra F R] (a b a' b' : κ → R) :
    Sum.elim a b ⬝ᵥ ((weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) *ᵥ Sum.elim a' b' =
      a ⬝ᵥ b' - a' ⬝ᵥ b := by
  simp only [weylM, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]
  simp [Matrix.map_neg, Matrix.neg_mulVec, dotProduct_comm b a', sub_eq_add_neg]


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
theorem darboux_change_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (c₁ c₂ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₂.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      GlobalTheory.SympChange.IsSymp G ∧ ∀ w, c₂.e w = GlobalTheory.SympChange.spAct G (c₁.e w) := by
  intro F E _ _ _ _ _ σ n d JX JW c₁ c₂ h₁ h₂
  classical
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _

  have honto : ∀ y z : Fin n × Fin d → F, ∃ x : Matrix (Fin n) (Fin d) E,
      c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro y z
    let I : Matrix (Fin n) (Fin d) E →ₗ[F] Matrix (Fin n) (Fin d) (AE F E) :=
      (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
    let L : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (c₁.e.toLinearMap.restrictScalars F).comp I
    have hL : ∀ x, L x = c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) := fun x => rfl
    let r : (Fin n × Fin d → F) →ₗ[F] (Fin n × Fin d → AF F) :=
      LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
    let R : ((Fin n × Fin d → F) × (Fin n × Fin d → F)) →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      LinearMap.prodMap r r
    have hR : ∀ y z, R (y, z) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) :=
      fun _ _ => rfl
    have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
    have hRinj : Function.Injective R := fun a b h =>
      Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
    have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
      Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
    have hLinj : Function.Injective L := c₁.e.injective.comp hIinj
    have hle : LinearMap.range L ≤ LinearMap.range R := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y', z', h⟩ := h₁ x
      exact ⟨(y', z'), by rw [hR, hL, h]⟩
    have hdim : Fintype.card (Fin n) * Fintype.card (Fin d) * Module.finrank F E =
        Fintype.card (Fin n × Fin d) + Fintype.card (Fin n × Fin d) := by
      have h1 := c₁.e.finrank_eq
      rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
      exact h1
    have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
      rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
        Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim]
    have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
    obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
    exact ⟨x, by rw [← hL, hx, hR]⟩

  let g : ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) ≃ₗ[AF F]
      ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) := c₁.e.symm.trans c₂.e
  have hgrat : ∀ y z : Fin n × Fin d → F, ∃ y' z' : Fin n × Fin d → F,
      g (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i)) := by
    intro y z
    obtain ⟨x, hx⟩ := honto y z
    obtain ⟨y', z', h⟩ := h₂ x
    exact ⟨y', z', by rw [← hx]; simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, h]⟩
  let S := LinearEquiv.sumArrowLequivProdArrow (Fin n × Fin d) (Fin n × Fin d) (AF F) (AF F)
  let φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) →ₗ[AF F] ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) :=
    (S.symm.toLinearMap.comp g.toLinearMap).comp S.toLinearMap
  have hφ : ∀ s, φ s = S.symm (g (S s)) := fun s => rfl
  have hent : ∀ i j, ∃ c : F, LinearMap.toMatrix' φ i j = algebraMap F (AF F) c := by
    intro i j
    rw [LinearMap.toMatrix'_apply]
    obtain ⟨y', z', h⟩ := hgrat (fun k => (Pi.single j (1 : F) : _ → F) (Sum.inl k))
      (fun k => (Pi.single j (1 : F) : _ → F) (Sum.inr k))
    have hS : S (Pi.single j 1) = (fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : _ → F) (Sum.inl k)),
        fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : _ → F) (Sum.inr k))) := by
      ext k <;> simp [S, Pi.single_apply, apply_ite]
    refine ⟨Sum.elim y' z' i, ?_⟩
    rw [hφ, hS, h]
    cases i <;> simp [S]
  obtain ⟨G, hG⟩ : ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      ∀ i j, LinearMap.toMatrix' φ i j = algebraMap F (AF F) (G i j) :=
    ⟨Matrix.of fun i j => (hent i j).choose, fun i j => (hent i j).choose_spec⟩
  have hGm : G.map (algebraMap F (AF F)) = LinearMap.toMatrix' φ := Matrix.ext fun i j => (hG i j).symm
  have hact : ∀ u, g u = spAct G u := by
    intro u
    have h1 : spAct G u = S (LinearMap.toMatrix' φ *ᵥ S.symm u) := by
      rw [← hGm]; rfl
    rw [h1, LinearMap.toMatrix'_mulVec, hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

  have hstd : ∀ u u' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
      S.symm u ⬝ᵥ (weylM.map (algebraMap F (AF F))) *ᵥ S.symm u' = u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 := by
    intro u u'
    obtain ⟨a, b⟩ := u
    obtain ⟨a', b'⟩ := u'
    have hs : ∀ p q : Fin n × Fin d → AF F, S.symm (p, q) = Sum.elim p q := fun p q => funext fun k => by
      cases k <;> simp [S]
    rw [hs, hs]
    exact sumElim_weylM_map a b a' b'
  have hkeep : ∀ u u' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
      (g u).1 ⬝ᵥ (g u').2 - (g u').1 ⬝ᵥ (g u).2 = u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 := by
    intro u u'
    have e2 := c₂.form (c₁.e.symm u) (c₁.e.symm u')
    have e1 := c₁.form (c₁.e.symm u) (c₁.e.symm u')
    simp only [LinearEquiv.apply_symm_apply] at e1
    simp only [g, LinearEquiv.trans_apply]
    rw [← e2, e1]
  refine ⟨G, ?_, fun w => ?_⟩
  · unfold IsSymp
    refine Matrix.map_injective hAinj ?_
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hGm]
    ext i j
    have key : ∀ s s' : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
        s ⬝ᵥ ((LinearMap.toMatrix' φ)ᵀ * weylM.map (algebraMap F (AF F)) * LinearMap.toMatrix' φ) *ᵥ s' =
          s ⬝ᵥ (weylM.map (algebraMap F (AF F))) *ᵥ s' := by
      intro s s'
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hφ, hφ, hstd, hkeep,
        ← hstd, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, Matrix.mulVec_single_one] using this
  · have := hact (c₁.e w)
    simpa [g] using this

end GlobalTheory.SympChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompareStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_darboux_coordinates_compare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (c₁ c₂ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₂.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      GlobalTheory.SympChange.IsSymp G ∧ ∀ w, c₂.e w = GlobalTheory.SympChange.spAct G (c₁.e w) := by
  first | exact @GlobalTheory.SympChange.darboux_change_rat | exact GlobalTheory.SympChange.darboux_change_rat | (intros; apply GlobalTheory.SympChange.darboux_change_rat <;> assumption)
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spAct_one {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)) :
    spAct (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [spAct, h1, Matrix.one_mulVec]
  rfl

theorem spAct_mul {R : Type} [CommRing R] [Algebra F R] (G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    spAct (G * G') w = spAct G (spAct G' w) := by
  have h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  conv_rhs => rw [spAct, h]
  simp only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]

variable [NumberField F]

theorem hasOp_one (ψ : AddChar (AF F) ℂ) : HasOp (κ := κ) ψ 1 := by
  refine ⟨LinearMap.id, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, Function.surjective_id, fun Φ h => h,
    fun w Φ _ => by simp [spAct_one], fun v => Submodule.map_id _, fun v φ _ h => h, fun v w φ _ => by simp [spAct_one],
    Filter.Eventually.of_forall fun v => rfl, fun f φ _ _ => rfl⟩

theorem hasOp_mul {ψ : AddChar (AF F) ℂ} {G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hG : HasOp ψ G) (hG' : HasOp ψ G') :
    HasOp ψ (G * G') := by
  obtain ⟨e, ei, ev, hs, hm, hh, hSB, hi, hl, hind, hp⟩ := hG
  obtain ⟨e', ei', ev', hs', hm', hh', hSB', hi', hl', hind', hp'⟩ := hG'
  have hmem : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev' v φ ∈ SB (κ → Fv F v) := fun v φ hφ => by
    rw [← hSB' v]; exact Submodule.mem_map_of_mem hφ
  refine ⟨e ∘ₗ e', ei.comp ei', fun v => ev v ∘ₗ ev' v, hs.comp hs', fun Φ h => hm _ (hm' _ h), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hh' w Φ hΦ, hh _ _ (hm' _ hΦ), spAct_mul]
  · intro v
    rw [Submodule.map_comp, hSB', hSB]
  · intro v φ hφ h0
    exact hi' v φ hφ (hi v _ (hmem v φ hφ) h0)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hl' v w φ hφ, hl v _ _ (hmem v φ hφ), spAct_mul]
  · filter_upwards [hind, hind'] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ hφv
    simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hp' f φ hφ hφv, hp _ _ (fun v => hmem v _ (hφ v))]
    filter_upwards [hφv, hind'] with v h1 h2
    rw [h1, h2]

theorem hasOp_of_mem_closure {ψ : AddChar (AF F) ℂ} (hgen : ∀ G ∈ gens (F := F) (κ := κ), HasOp ψ G) :
    ∀ G ∈ Submonoid.closure (gens (F := F) (κ := κ)), HasOp ψ G := fun G hG =>
  Submonoid.closure_induction (fun x hx => hgen x hx) (hasOp_one ψ) (fun _ _ _ _ hx hy => hasOp_mul hx hy) hG

theorem locCo_eq {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (c₁ c₂ : Darboux B κ)
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (h : ∀ w, c₂.e w = spAct G (c₁.e w)) (v : Pl (F := F)) (γ : W) :
    GlobalTheory.LatVac.locCo c₂ v γ = spAct G (GlobalTheory.LatVac.locCo c₁ v γ) := by
  have key : ∀ (x : κ ⊕ κ → AF F) (i : κ ⊕ κ), evFin F v ((G.map (algebraMap F (AF F)) *ᵥ x) i) =
      (G.map (algebraMap F (Fv F v)) *ᵥ fun j => evFin F v (x j)) i := by
    intro x i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  have hs : ∀ a b : κ → AF F, (fun j => evFin F v (Sum.elim a b j)) =
      Sum.elim (fun k => evFin F v (a k)) (fun k => evFin F v (b k)) := by
    intro a b; funext j; cases j <;> rfl
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, spAct, key, hs]

theorem acts_unique' (v : Pl (F := F)) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hR : Rest (evFin F v) φ R) {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  have e := (h₁ R hR).symm.trans (h₂ R hR)
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

end GlobalTheory.SympChange

open GlobalTheory.SympChange in
theorem GlobalTheory.SympChange.change_of_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hM co hco
  obtain ⟨G, hGs, hGe⟩ := GlobalTheory.T.rational_darboux_coordinates_compare F E σ n d X.J W.J M.co co hM.rat hco
  obtain ⟨hunr, hnt⟩ := GlobalTheory.T.standard_character_almost_unramified F B.ψ hB.std
  have hgen : ∀ G ∈ gens (F := F) (κ := Fin n × Fin d), HasOp B.ψ G := by
    rintro G ((⟨A, hA, rfl⟩ | ⟨S, hS, rfl⟩) | hG)
    · exact GlobalTheory.T.weil_operator_for_levi_matrix F B.ψ hB.std hunr hnt _ A hA
    · exact GlobalTheory.T.weil_operator_for_unipotent_matrix F B.ψ hB.std hunr hnt _ S hS
    · rw [Set.mem_singleton_iff.mp hG]; exact GlobalTheory.T.weil_operator_for_weyl_element F B.ψ hB.std hunr hnt _
  obtain ⟨e, ei, ev, hsurj, hmaps, hheis, hSB, hinj, hloc, hind, hpure⟩ :=
    hasOp_of_mem_closure hgen G (GlobalTheory.T.symplectic_group_generated_by_elementary F _ G hGs)
  refine ⟨e, ei, ev, hsurj, hmaps, ?_, hSB, ?_, ?_, ?_⟩
  · intro u Φ hΦ
    show e (schr B.ψ (M.co.e u) Φ) = schr B.ψ (co.e u) (e Φ)
    rw [hheis _ Φ hΦ, hGe]
  · intro v
    obtain ⟨hvSB, hvne, θ, hθ, hγ⟩ := hM.vac v
    have hevSB : ev v (M.vac v) ∈ SB _ := by rw [← hSB v]; exact Submodule.mem_map_of_mem hvSB
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin n × Fin d) v
    refine ⟨hevSB, fun h0 => hvne (hinj v _ hvSB h0), θ, hθ, fun γ hγm => ?_⟩
    have hat : At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγm
    have h1 := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat (M.vac v)
    have heq := acts_unique' v hR0 (hR _ hvSB) h1 (hγ γ hγm)
    have h3 := GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v γ hat (ev v (M.vac v))
    have hcoord : GlobalTheory.LatVac.locCo co v γ = spAct G (GlobalTheory.LatVac.locCo M.co v γ) :=
      locCo_eq M.co co G hGe v γ
    rw [hcoord, ← hloc v _ _ hvSB, heq, map_smul] at h3
    exact h3
  · filter_upwards [hM.std, hind] with v h1 h2
    rw [h1]; exact h2
  · intro f φ hφ hφv
    refine hpure f φ hφ ?_
    filter_upwards [hφv, hM.std] with v h1 h2
    rw [h1, h2]; rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeBij

open GlobalTheory.SympChange GlobalTheory.LeviOp GlobalTheory.SympUnip GlobalTheory.AdelicSvNQuad GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

section Levi

variable {F : Type} [Field F] [NumberField F] {κ : Type}


open scoped Classical in
theorem levi_mapsTo [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F) (hA : IsUnit A.det) :
    ∀ Φ ∈ schA F κ, LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) Φ ∈ schA F κ := by
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) =
        pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA) := by
    intro f g
    funext x
    simp only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    congr 1
    · congr 1
      funext i
      exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
    · congr 1
      funext i
      exact hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i
  have hle : schA F κ ≤ (schA F κ).comap
      (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    show _ ∈ schA F κ
    rw [key]
    exact Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩
  exact fun Φ hΦ => hle hΦ


open scoped Classical in
theorem bijOn_levi [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F) (hA : IsUnit A.det) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x))
      (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) := by
  have hA' : IsUnit A⁻¹.det := Matrix.isUnit_nonsing_inv_det A hA
  have hm' := levi_mapsTo A⁻¹ hA'
  rw [Matrix.nonsing_inv_nonsing_inv A hA] at hm'
  refine bijOn_of_inv _ _ (levi_mapsTo A hA) hm' (fun Φ _ => ?_) (fun Φ _ => ?_)
  · funext x
    simp only [LinearMap.funLeft_apply, Matrix.mulVec_mulVec, map_inv_mul _ A hA, Matrix.one_mulVec]
  · funext x
    simp only [LinearMap.funLeft_apply, Matrix.mulVec_mulVec, map_mul_inv _ A hA, Matrix.one_mulVec]

end Levi


open scoped Classical in
theorem hasOpB_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    HasOpB ψ (GlobalTheory.SympChange.leviM A) := by
  intro F _ _ ψ _ _ _ κ _ _ A hA
  classical
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x),
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L,
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    simp
  · have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
        LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) =
          pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA) := by
      intro f g
      funext x
      simp only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      congr 1
      · congr 1
        funext i
        exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
      · congr 1
        funext i
        exact hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i
    have hle : schA F κ ≤ (schA F κ).comap
        (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, g, hg, rfl⟩
      show _ ∈ schA F κ
      rw [key]
      exact Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩
    exact fun Φ hΦ => hle hΦ
  · intro w Φ _
    exact schr_levi ψ A hA w Φ
  · intro v
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => sb_comp (homeo _ A hA) hφ) ?_
    intro φ hφ
    refine ⟨φ ∘ (homeo (algebraMap F (Fv F v)) A hA).symm, sb_comp _ hφ, ?_⟩
    funext x
    simp only [LinearMap.funLeft_apply, Function.comp_apply]
    exact congrArg φ ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x)
  · intro v φ _ h
    funext x
    have := congrFun h ((homeo (algebraMap F (Fv F v)) A hA).symm x)
    simp only [LinearMap.funLeft_apply, Pi.zero_apply] at this
    have hx : A⁻¹.map (algebraMap F (Fv F v)) *ᵥ (homeo (algebraMap F (Fv F v)) A hA).symm x = x :=
      (homeo (algebraMap F (Fv F v)) A hA).apply_symm_apply x
    rw [hx] at this
    exact this
  · intro v w φ _
    exact schr_levi (GlobalTheory.LatVac.psiAt ψ v) A hA w φ
  · filter_upwards [eventually_int A, eventually_int A⁻¹] with v hA1 hA2
    funext x
    have hiff : (∀ i, (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
      constructor
      · intro h i
        have e : x = A.map (algebraMap F (Fv F v)) *ᵥ (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) :=
          ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x).symm
        rw [e]
        exact mulVec_mem A hA1 _ h i
      · intro h i
        exact mulVec_mem A⁻¹ hA2 x h i
    show Set.indicator _ _ _ = Set.indicator _ _ _
    by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hiff.2 hx),
        Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show _ ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from mt hiff.1 hx),
        Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
  · intro f φ _ _
    funext x
    simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply]
    congr 1
    · congr 1
      funext i
      exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
    · refine finprod_congr fun v => congrArg (φ v) ?_
      funext i
      exact hom_mulVec (evFin F v).toRingHom (algebraMap F (AF F)) (algebraMap F (Fv F v))
        (RingHom.ext fun c => (evFin F v).commutes c) A⁻¹ x i
  · exact bijOn_levi A hA


open scoped Classical in
theorem hasOpB_unipM : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    (∀ᶠ v in cofinite, PsiUnr ψ v) → (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (S : Matrix κ κ F), S.transpose = S →
    HasOpB ψ (GlobalTheory.SympChange.unipM S) := by
  intro F _ _ ψ hψ hunr _ κ _ _ S hS
  classical
  have evFin_invOf_two (v : Pl F) : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  let A : Matrix κ κ (AF F) := -S.map (algebraMap F (AF F))
  let Av : ∀ v : Pl (F := F), Matrix κ κ (Fv F v) := fun v => -S.map (algebraMap F (Fv F v))
  have hAv : ∀ v, A.map (evFin F v : AF F →+* Fv F v) = Av v := fun v => by
    refine Matrix.ext fun i j => ?_
    change evFin F v (-algebraMap F (AF F) (S i j)) = -algebraMap F (Fv F v) (S i j)
    rw [map_neg, AlgHom.commutes]
  let q : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
  let hi := q (⅟2)
  let Ai := A.map q
  refine ⟨mulR ψ (⅟2) A, SchwartzMap.smulLeftCLM ℂ (archMul hi Ai),
    fun v => mulR (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v), fun f => ?_, mulQ_mem ψ hψ _ A,
    fun w Φ _ => mulR_schr ψ S hS w Φ, fun v => ?_, fun v φ _ h0 => ?_,
    fun v w φ _ => mulR_schr _ S hS w φ, ?_, fun f φ _ hφ => ?_, ?_⟩
  · refine ⟨SchwartzMap.smulLeftCLM ℂ (archMul hi (-Ai)) f, SchwartzMap.ext fun y => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
      SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_smul, archMul, archMul, eChar_apply,
      eChar_apply, ← Complex.exp_add, quad_neg, map_neg, neg_neg]
    rw [show ∀ a : ℂ, a = 0 → Complex.exp a • f y = f y from fun a ha => by rw [ha, Complex.exp_zero, one_smul]]
    push_cast
    ring
  · have hlc := psiAt_isLocallyConstant ψ hψ.1 v
    refine le_antisymm ?_ fun φ hφ => ⟨mulR _ (⅟2) (-Av v) φ, mulR_mem hlc _ _ hφ, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      exact mulR_mem hlc _ _ hφ
    · have := mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-Av v) φ
      rwa [neg_neg] at this
  · rw [← mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v) φ]
    exact (congrArg _ h0).trans (map_zero _)
  · have h2 : ∀ᶠ v : Pl F in cofinite, evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := eventually_evFin _
    have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i j, evFin F v (A i j) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j => eventually_evFin (A i j)
    filter_upwards [hunr, h2, h3] with v hv h2 h3
    funext x
    rw [mulR_apply]
    by_cases hx : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    · rw [evFin_invOf_two v] at h2
      have h4 := (hv 1).2 (one_mem _) _ (quad_mem (A := Av v) h2 (fun i j => by rw [← hAv v]; exact h3 i j) hx)
      rw [one_mul] at h4
      rw [GlobalTheory.LatVac.psiAt_apply, h4, one_mul]
    · rw [indO, Set.indicator_of_notMem hx, mul_zero]
  · funext x
    have hfin : (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
      have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
        eventually_all.2 fun i => eventually_evFin (x i)
      have h4 : ∀ᶠ v : Pl F in cofinite, (φ v fun i => evFin F v (x i)) = 1 := by
        filter_upwards [hφ, h3] with v hv h3
        rw [hv, indO, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3)]
        rfl
      exact h4
    have hq : ∀ v : Pl (F := F), evalV F v (p2 (quad (⅟2) A x)) = quad (⅟2) (Av v) fun i => evFin F v (x i) := fun v => by
      have := map_quad (evFin F v : AF F →+* Fv F v) (⅟2) A x
      rw [hAv] at this
      exact this.trans (congrArg (fun t => quad t (Av v) fun i => evFin F v (x i)) (evFin_invOf_two v))
    obtain ⟨hs, hp⟩ := finChar_eq_finprod ψ hψ.1 (p2 (quad (⅟2) A x))
    simp only [hq] at hs hp
    have h3 : ψ (mk (p1 (quad (⅟2) A x)) 0) = archMul hi Ai fun i => evI F (x i) := by
      have e1 : evI F (mk (p1 (quad (⅟2) A x)) 0) = quad hi Ai fun i => evI F (x i) := map_quad q (⅟2) A x
      rw [hψ.2.2 _ (at_mk _), e1, archMul, eChar_apply]
      congr 1
      push_cast
      ring
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mulR_apply]
    rw [finprod_mul_distrib hs hfin, ← hp, map_eq_mul ψ, h3,
      SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]
    ring
  · exact bijOn_of_inv (mulR ψ (⅟2) A) (mulR ψ (⅟2) (-A)) (mulQ_mem ψ hψ _ A) (mulQ_mem ψ hψ _ (-A))
      (fun Φ _ => mulR_neg ψ (⅟2) A Φ) (fun Φ _ => by simpa only [neg_neg] using mulR_neg ψ (⅟2) (-A) Φ)

end GlobalTheory.SympChangeBij


open GlobalTheory.SympChange GlobalTheory.SympChangeBij in
open scoped Classical in
theorem GlobalTheory.SympChangeBij.change_of_coordinates_bij : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) ∧
        Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hM co hco
  obtain ⟨G, hGs, hGe⟩ := GlobalTheory.T.rational_darboux_coordinates_compare F E σ n d X.J W.J M.co co hM.rat hco
  obtain ⟨hunr, hnt⟩ := GlobalTheory.T.standard_character_almost_unramified F B.ψ hB.std
  have hgen : ∀ G ∈ gens (F := F) (κ := Fin n × Fin d), HasOpB B.ψ G := by
    rintro G ((⟨A, hA, rfl⟩ | ⟨S, hS, rfl⟩) | hG)
    · exact hasOpB_levi F B.ψ hB.std hunr hnt _ A hA
    · exact hasOpB_unipM F B.ψ hB.std hunr hnt _ S hS
    · rw [Set.mem_singleton_iff.mp hG]; exact GlobalTheory.T.weyl_element_operator_bijective F B.ψ hB.std hunr hnt _
  obtain ⟨e, ei, ev, hsurj, hmaps, hheis, hSB, hinj, hloc, hind, hpure, hbij⟩ :=
    hasOpB_of_mem_closure hgen G (GlobalTheory.T.symplectic_group_generated_by_elementary F _ G hGs)
  refine ⟨e, ei, ev, hsurj, hmaps, ?_, hSB, ?_, ?_, ?_, hbij⟩
  · intro u Φ hΦ
    show e (schr B.ψ (M.co.e u) Φ) = schr B.ψ (co.e u) (e Φ)
    rw [hheis _ Φ hΦ, hGe]
  · intro v
    obtain ⟨hvSB, hvne, θ, hθ, hγ⟩ := hM.vac v
    have hevSB : ev v (M.vac v) ∈ SB _ := by rw [← hSB v]; exact Submodule.mem_map_of_mem hvSB
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin n × Fin d) v
    refine ⟨hevSB, fun h0 => hvne (hinj v _ hvSB h0), θ, hθ, fun γ hγm => ?_⟩
    have hat : At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγm
    have h1 := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat (M.vac v)
    have heq := acts_unique' v hR0 (hR _ hvSB) h1 (hγ γ hγm)
    have h3 := GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v γ hat (ev v (M.vac v))
    have hout : schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v γ) (ev v (M.vac v)) =
        B.ψ (⅟2 * symp (cA σ) ((inclR (AF F)) θ) (incM F X.J) (incM F W.J) γ γ) • ev v (M.vac v) := by
      calc
        _ = schr (GlobalTheory.LatVac.psiAt B.ψ v) (spAct G (GlobalTheory.LatVac.locCo M.co v γ)) (ev v (M.vac v)) := congrArg (fun w => schr _ w _) (locCo_eq M.co co G hGe v γ)
        _ = ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) (M.vac v)) := (hloc v _ _ hvSB).symm
        _ = _ := by rw [heq, map_smul]
    exact hout ▸ h3
  · filter_upwards [hM.std, hind] with v h1 h2
    rw [h1]; exact h2
  · intro f φ hφ hφv
    refine hpure f φ hφ ?_
    filter_upwards [hφv, hM.std] with v h1 h2
    rw [h1, h2]; rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModelStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_coords_good_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) ∧
        Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) := by
  first | exact @GlobalTheory.SympChangeBij.change_of_coordinates_bij | exact GlobalTheory.SympChangeBij.change_of_coordinates_bij | (intros; apply GlobalTheory.SympChangeBij.change_of_coordinates_bij <;> assumption)
end
