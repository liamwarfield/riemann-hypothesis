module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacquetBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem hasFiniteLength_twist_iff (ρ : Representation F G V) (χ : G →* Fˣ) :
    HasFiniteLength (twist ρ χ) ↔ HasFiniteLength ρ := by
  let φ : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.apply_mem_toSubmodule g hv
        rw [twist_apply] at h1
        have h2 := S.toSubmodule.smul_mem ((χ g : F)⁻¹) h1
        rwa [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h2⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        rw [twist_apply]
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [hasFiniteLength_iff_wellFounded, hasFiniteLength_iff_wellFounded]
  exact and_congr ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.toOrderEmbedding.wellFoundedGT⟩ ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedLT,
    fun _ => φ.toOrderEmbedding.wellFoundedLT⟩

theorem hasFiniteLength_of_surjective {ρ : Representation F G V} {σ : Representation F G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (h : HasFiniteLength ρ) :
    HasFiniteLength σ :=
  IsFiniteLength.of_surjective h
    (f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf

end General

section Blocks

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem mem_unipRad_iff_blk {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ g ∈ parab R e ∧
      ∀ i j, blk e i = blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  refine and_congr_right fun _ => ⟨fun h i j hij => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    subst hij
    rw [h a x y]
    simp [Matrix.one_apply, e.injective.eq_iff]
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply, e.injective.eq_iff]


omit [LinearOrder α] in
theorem leviEmb_apply_of_blk_ne [DecidableEq α] (e : (Σ a, m a) ≃ n) (g : Levi R m) {i j : n}
    (h : blk e i ≠ blk e j) : (leviEmb R e g : Matrix n n R) i j = 0 := by
  letI : DecidableEq α := Classical.typeDecidableEq α
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  have hab : a ≠ b := by simpa using h
  simpa [leviEmb, Matrix.reindex_apply] using
    (Matrix.blockDiagonal'_apply_ne (fun c => (g c : Matrix (m c) (m c) R)) x y hab)

theorem leviEmb_leviProj_of_blk (e : (Σ a, m a) ≃ n) (p : parab R e)
    (h : ∀ i j, blk e i ≠ blk e j → ((p : GL n R) : Matrix n n R) i j = 0) :
    leviEmb R e (leviProj R e p) = p := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    simp [leviEmb, Matrix.reindex_apply, leviProj_apply]
  · have hblk : blk e (e ⟨a, x⟩) ≠ blk e (e ⟨b, y⟩) := by simpa using hab
    rw [leviEmb_apply_of_blk_ne e _ hblk, h _ _ hblk]

theorem leviProj_eq_of_coe_eq (e : (Σ a, m a) ≃ n) (p : parab R e) (g : Levi R m)
    (h : (p : GL n R) = leviEmb R e g) : leviProj R e p = g := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, h]
  simp [leviEmb, Matrix.reindex_apply]

end Blocks

section Transport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_of_transport (e : (Σ a, m a) ≃ n) (e' : (Σ b, m' b) ≃ n')
    (Φ : GL n' k →* GL n k) (Ψ : Levi k m' →* Levi k m) (hΨ : Function.Surjective Ψ)
    (hU : ∀ u ∈ unipRad k e', Φ u ∈ unipRad k e)
    (hL : ∀ g, Φ (leviEmb k e' g) = leviEmb k e (Ψ g)) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e' (π.comp Φ))) : HasFiniteLength (jacU e π) := by
  have hle : twKer (π.comp Φ) (unipRad k e') 1 ≤ twKer π (unipRad k e) 1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨Φ u, hU u u.2⟩, v, by simp⟩
  let f : (jacU e' (π.comp Φ)).IntertwiningMap ((jacU e π).comp Ψ) :=
    ⟨(twKer (π.comp Φ) (unipRad k e') 1).mapQ (twKer π (unipRad k e) 1) LinearMap.id hle,
      fun g => by
        ext v
        show Submodule.Quotient.mk (π (Φ (leviEmb k e' g)) v) =
          (Submodule.Quotient.mk (π (leviEmb k e (Ψ g)) v) : Jacquet π (unipRad k e))
        rw [hL]⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  rw [← hasFiniteLength_comp_iff _ Ψ hΨ]
  exact hasFiniteLength_of_surjective f hf h

end Transport

section Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_reindex (e : (Σ b, m' b) ≃ n') (ψ : n' ≃ n)
    (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e (π.comp
      (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom))) :
    HasFiniteLength (jacU (e.trans ψ) π) := by
  set Φ : GL n' k →* GL n k := (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom
  have hΦ : ∀ (g : GL n' k) (i j : n), (Φ g : Matrix n n k) i j = (g : Matrix n' n' k) (ψ.symm i) (ψ.symm j) :=
    fun _ _ _ => rfl
  refine hasFiniteLength_jacU_of_transport (e.trans ψ) e Φ (MonoidHom.id _) Function.surjective_id
    (fun u hu => ?_) (fun g => ?_) π h
  · rw [mem_unipRad] at hu ⊢
    refine ⟨mem_parab_iff.2 fun a b x y hab => ?_, fun a x y => ?_⟩
    · rw [hΦ]
      simpa using mem_parab_iff.1 hu.1 a b x y hab
    · rw [hΦ]
      simpa using hu.2 a x y
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [hΦ]
    rfl

end Stages

end GlobalTheory.JacquetBlocks

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlocksParabolicInductionFiniteLength
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory.BlockReorder

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

abbrev NonemptyBlockIndex (m : α → Type) [∀ a, Fintype (m a)] : Type := {a : α // 0 < Fintype.card (m a)}

abbrev numBlocks (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] : ℕ := Fintype.card (NonemptyBlockIndex m)

def neOrder (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] : Fin (numBlocks m) ≃o NonemptyBlockIndex m :=
  monoEquivOfFin (NonemptyBlockIndex m) rfl

def blockSize (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] (i : Fin (numBlocks m)) : ℕ :=
  Fintype.card (m (neOrder m i).1)

def blockNum (i : Fin (numBlocks m)) : Fin (blockSize m i) ≃ m (neOrder m i).1 := (Fintype.equivFin _).symm

def stdSigma (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] :
    (Σ i, Fin (blockSize m i)) ≃ (Σ a, m a) :=
  ((Equiv.sigmaCongrRight blockNum).trans (Equiv.sigmaCongrLeft (β := fun b : NonemptyBlockIndex m => m b.1) (neOrder m).toEquiv)).trans
    (Equiv.sigmaSubtypeEquivOfSubset m (fun a => 0 < Fintype.card (m a))
      fun _ x => Fintype.card_pos_iff.2 ⟨x⟩)

@[simp] theorem stdSigma_apply (i : Fin (numBlocks m)) (u : Fin (blockSize m i)) :
    stdSigma m ⟨i, u⟩ = ⟨(neOrder m i).1, blockNum i u⟩ := rfl

def stdIdx (e : (Σ a, m a) ≃ n) : Fin (∑ i, blockSize m i) ≃ n :=
  finSigmaFinEquiv.symm.trans ((stdSigma m).trans e)

@[simp] theorem stdIdx_symm_apply (e : (Σ a, m a) ≃ n) (i : Fin (numBlocks m)) (u : Fin (blockSize m i)) :
    (stdIdx e).symm (e ⟨(neOrder m i).1, blockNum i u⟩) = finSigmaFinEquiv ⟨i, u⟩ := by
  rw [Equiv.symm_apply_eq, stdIdx]
  simp

variable (R : Type) [CommRing R]

def glIso (e : (Σ a, m a) ≃ n) : GL (Fin (∑ i, blockSize m i)) R ≃* GL n R :=
  Units.mapEquiv (reindexAlgEquiv R R (stdIdx e)).toMulEquiv

variable {R}

theorem val_glIso (e : (Σ a, m a) ≃ n) (g : GL (Fin (∑ i, blockSize m i)) R) (x y : n) :
    (glIso R e g : Matrix n n R) x y = (g : Matrix _ _ R) ((stdIdx e).symm x) ((stdIdx e).symm y) := rfl

variable (R)

theorem glIso_mem_parab (e : (Σ a, m a) ≃ n) {g : GL (Fin (∑ i, blockSize m i)) R}
    (hg : g ∈ parab R (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _)) : glIso R e g ∈ parab R e := by
  refine mem_parab.2 fun x y hxy => ?_
  obtain ⟨⟨i, u⟩, rfl⟩ := ((stdSigma m).trans e).surjective x
  obtain ⟨⟨j, v⟩, rfl⟩ := ((stdSigma m).trans e).surjective y
  simp only [Equiv.trans_apply, stdSigma_apply, blk_apply] at hxy
  have hji : j < i := (neOrder m).lt_iff_lt.1 (Subtype.coe_lt_coe.1 hxy)
  simp only [Equiv.trans_apply, stdSigma_apply, val_glIso, stdIdx_symm_apply]
  exact mem_parab_iff.1 hg i j u v hji

def leviMap (e : (Σ a, m a) ≃ n) : Levi R (fun i => Fin (blockSize m i)) →* Levi R m :=
  (leviProj R e).comp (((glIso R e).toMonoidHom.comp (leviEmb R finSigmaFinEquiv)).codRestrict (parab R e)
    fun g => glIso_mem_parab R e (leviEmb_mem_parab R _ g))

variable {R}

theorem leviMap_apply (e : (Σ a, m a) ≃ n) (g : Levi R (fun i => Fin (blockSize m i))) (a : α) (x y : m a) :
    (leviMap R e g a : Matrix (m a) (m a) R) x y =
      (leviEmb R finSigmaFinEquiv g : Matrix _ _ R) ((stdIdx e).symm (e ⟨a, x⟩)) ((stdIdx e).symm (e ⟨a, y⟩)) :=
  rfl

@[simp] theorem leviMap_apply_num (e : (Σ a, m a) ≃ n) (g : Levi R (fun i => Fin (blockSize m i))) (i : Fin (numBlocks m))
    (u v : Fin (blockSize m i)) :
    (leviMap R e g (neOrder m i).1 : Matrix _ _ R) (blockNum i u) (blockNum i v) = (g i : Matrix _ _ R) u v := by
  rw [leviMap_apply, stdIdx_symm_apply, stdIdx_symm_apply, leviEmb_apply_same]

theorem levi_ext {g h : Levi R m}
    (H : ∀ (i : Fin (numBlocks m)) (u v : Fin (blockSize m i)),
      (g (neOrder m i).1 : Matrix _ _ R) (blockNum i u) (blockNum i v) = (h (neOrder m i).1 : Matrix _ _ R) (blockNum i u) (blockNum i v)) :
    g = h := by
  funext a
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨i, hi⟩ := (neOrder m).surjective ⟨a, Fintype.card_pos_iff.2 ⟨x⟩⟩
  have ha : (neOrder m i).1 = a := congrArg Subtype.val hi
  subst ha
  obtain ⟨u, rfl⟩ := (blockNum i).surjective x
  obtain ⟨v, rfl⟩ := (blockNum i).surjective y
  exact H i u v

theorem leviProj_glIso (e : (Σ a, m a) ≃ n)
    (p : parab R (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _)) :
    leviProj R e ⟨glIso R e p, glIso_mem_parab R e p.2⟩ =
      leviMap R e (leviProj R finSigmaFinEquiv p) := by
  refine levi_ext fun i u v => ?_
  rw [leviMap_apply_num, leviProj_apply, leviProj_apply]
  simp only [val_glIso, stdIdx_symm_apply]

theorem leviMap_surjective (e : (Σ a, m a) ≃ n) : Function.Surjective (leviMap R e) := by
  intro h
  refine ⟨fun i => Units.map (reindexAlgEquiv R R (blockNum i).symm).toRingEquiv.toMonoidHom (h (neOrder m i).1),
    levi_ext fun i u v => ?_⟩
  rw [leviMap_apply_num]
  simp [reindexAlgEquiv_apply]

theorem continuous_glIso [TopologicalSpace R] (e : (Σ a, m a) ≃ n) : Continuous (glIso R e) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun x y => ?_, continuous_matrix fun x y => ?_⟩
  · exact Units.continuous_val.matrix_elem _ _
  · have : ∀ g : GL (Fin (∑ i, blockSize m i)) R, (((glIso R e g)⁻¹ : GL n R) : Matrix n n R) x y =
        ((g⁻¹ : GL _ R) : Matrix _ _ R) ((stdIdx e).symm x) ((stdIdx e).symm y) := fun g => by
      rw [← map_inv]; rfl
    simp only [this]
    exact Units.continuous_coe_inv.matrix_elem _ _

theorem continuous_leviMap [TopologicalSpace R] [IsTopologicalRing R] (e : (Σ a, m a) ≃ n) :
    Continuous (leviMap R e) := by
  refine continuous_pi fun a => Units.continuous_iff.2 ⟨continuous_matrix fun x y => ?_,
    continuous_matrix fun x y => ?_⟩
  · exact (Units.continuous_val.comp (continuous_leviEmb R _)).matrix_elem _ _
  · have : ∀ g : Levi R (fun i => Fin (blockSize m i)), (((leviMap R e g a)⁻¹ : GL (m a) R) : Matrix _ _ R) x y =
        (((leviEmb R finSigmaFinEquiv g)⁻¹ : GL _ R) : Matrix _ _ R) ((stdIdx e).symm (e ⟨a, x⟩))
          ((stdIdx e).symm (e ⟨a, y⟩)) := fun g => by
      rw [← Pi.inv_apply, ← map_inv, leviMap_apply, map_inv]
    simp only [this]
    exact (Units.continuous_coe_inv.comp (continuous_leviEmb R _)).matrix_elem _ _

end GlobalTheory.BlockReorder

namespace GlobalTheory.BlockReorder

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem prod_neOrder {M : Type} [CommMonoid M] (F : α → M) (hF : ∀ a, Fintype.card (m a) = 0 → F a = 1) :
    ∏ a, F a = ∏ i : Fin (numBlocks m), F (neOrder m i).1 := by
  rw [← Finset.prod_filter_of_ne (p := fun a => 0 < Fintype.card (m a))
    (fun a _ h => Nat.pos_of_ne_zero fun h0 => h (hF a h0)),
    ← Finset.prod_subtype_eq_prod_filter, Finset.subtype_univ]
  exact ((neOrder m).toEquiv.prod_comp (fun b : NonemptyBlockIndex m => F b.1)).symm

theorem sum_neOrder {M : Type} [AddCommMonoid M] (F : α → M) (hF : ∀ a, Fintype.card (m a) = 0 → F a = 0) :
    ∑ a, F a = ∑ i : Fin (numBlocks m), F (neOrder m i).1 := by
  rw [← Finset.sum_filter_of_ne (p := fun a => 0 < Fintype.card (m a))
    (fun a _ h => Nat.pos_of_ne_zero fun h0 => h (hF a h0)),
    ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  exact ((neOrder m).toEquiv.sum_comp (fun b : NonemptyBlockIndex m => F b.1)).symm

theorem modExp_neOrder (i : Fin (numBlocks m)) : modExp m (neOrder m i).1 = modExp (fun j => Fin (blockSize m j)) i := by
  unfold modExp
  simp only [Finset.sum_filter]
  rw [sum_neOrder (m := m) (fun b => if (neOrder m i).1 < b then (Fintype.card (m b) : ℤ) else 0)
      (fun b hb => by simp [hb]),
    sum_neOrder (m := m) (fun b => if b < (neOrder m i).1 then (Fintype.card (m b) : ℤ) else 0)
      (fun b hb => by simp [hb])]
  have hc : ∀ j : Fin (numBlocks m), (Fintype.card (Fin (blockSize m j)) : ℤ) = Fintype.card (m (neOrder m j).1) :=
    fun j => by rw [Fintype.card_fin]; rfl
  simp only [hc, OrderIso.lt_iff_lt, Subtype.coe_lt_coe]

variable {R : Type} [CommRing R]

theorem det_eq_one_of_card_eq_zero {a : α} (h : Fintype.card (m a) = 0) (g : GL (m a) R) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  haveI : IsEmpty (m a) := Fintype.card_eq_zero_iff.1 h
  ext
  simp [Matrix.det_isEmpty]

theorem det_leviMap (e : (Σ a, m a) ≃ n) (g : Levi R (fun i => Fin (blockSize m i))) (i : Fin (numBlocks m)) :
    Matrix.GeneralLinearGroup.det (leviMap R e g (neOrder m i).1) = Matrix.GeneralLinearGroup.det (g i) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  have : (leviMap R e g (neOrder m i).1 : Matrix _ _ R) =
      (g i : Matrix _ _ R).submatrix (blockNum i).symm (blockNum i).symm := by
    ext x y
    obtain ⟨u, rfl⟩ := (blockNum i).surjective x
    obtain ⟨v, rfl⟩ := (blockNum i).surjective y
    simp
  rw [this, Matrix.det_submatrix_equiv_self]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_leviMap (e : (Σ a, m a) ≃ n) (g : Levi k (fun i => Fin (blockSize m i))) :
    deltaHalf k m (leviMap k e g) = deltaHalf k (fun i => Fin (blockSize m i)) g := by
  rw [deltaHalf_apply, deltaHalf_apply, prod_neOrder (m := m) _ fun a ha => by
    rw [det_eq_one_of_card_eq_zero ha, map_one]]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [det_leviMap, modExp_neOrder]

end GlobalTheory.BlockReorder

namespace GlobalTheory.BlockReorder

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    IndSp e ρ →ₗ[ℂ] IndSp (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e)) where
  toFun f := ⟨⟨fun g => f.1.1 (glIso k e g), fun p g => by
      show f.1.1 (glIso k e ((p : GL _ k) * g)) =
        (deltaHalf k (fun i => Fin (blockSize m i)) (leviProj k finSigmaFinEquiv p) : ℂ) •
          ρ (leviMap k e (leviProj k finSigmaFinEquiv p)) (f.1.1 (glIso k e g))
      rw [map_mul, ← deltaHalf_leviMap e, ← leviProj_glIso]
      exact parInd_law e ρ f ⟨glIso k e p, glIso_mem_parab k e p.2⟩ (glIso k e g)⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((continuous_glIso e).continuousAt.preimage_mem_nhds
        (t := {g : GL n k | ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) g f.1 = f.1})
        (by rw [map_one]; exact IsOpen.mem_nhds f.2 (by simp))) fun g hg => by
      have hg' : ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) (glIso k e g) f.1 = f.1 := hg
      apply Subtype.ext
      funext x
      show f.1.1 (glIso k e (x * g)) = f.1.1 (glIso k e x)
      rw [map_mul]
      exact congrFun (congrArg Subtype.val hg') (glIso k e x))⟩
  map_add' f f' := rfl
  map_smul' c f := rfl

def pullMap (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Representation.IntertwiningMap ((parInd e ρ).comp (glIso k e).toMonoidHom)
      (parInd (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e))) where
  toLinearMap := pullInd e ρ
  isIntertwining' g := by
    refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    change (parInd e ρ (glIso k e g) f).1.1 (glIso k e x) =
      (parInd finSigmaFinEquiv (ρ.comp (leviMap k e)) g (pullInd e ρ f)).1.1 x
    rw [parInd_apply, parInd_apply]
    change f.1.1 (glIso k e x * glIso k e g) = f.1.1 (glIso k e (x * g))
    rw [map_mul]

theorem pullInd_injective (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Function.Injective (pullInd e ρ) := by
  intro f f' h
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  obtain ⟨y, rfl⟩ := (glIso k e).surjective x
  exact congrFun (congrArg (fun F : IndSp _ _ => F.1.1) h) y

theorem hasFiniteLength_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    (h : HasFiniteLength (parInd (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e)))) :
    HasFiniteLength (parInd e ρ) := by
  have h1 : HasFiniteLength ((parInd e ρ).comp (glIso k e).toMonoidHom) :=
    IsFiniteLength.of_injective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (pullMap e ρ))
      (fun x y hxy => pullInd_injective e ρ hxy)
  exact (hasFiniteLength_comp_iff _ _ (glIso k e).surjective).1 h1

end GlobalTheory.BlockReorder

namespace GlobalTheory


end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.CupSpec

variable {R : Type} [CommRing R]

theorem free_ext {P : PSh} {G : Shv R} (a b : (free R).obj P ⟶ G)
    (h : ∀ U x, Sec.map a (freeGen R P U x) = Sec.map b (freeGen R P U x)) : a = b := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  exact h U.unop x.down

theorem free_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let η : (freeP R).obj P ⟶ F.obj :=
    { app := fun U => ModuleCat.freeDesc (TypeCat.ofHom fun x => a U.unop x.down)
      naturality := fun U V g => by
        apply ModuleCat.free_hom_ext
        intro x
        change (ModuleCat.freeDesc _) ((ModuleCat.free _).map _ (ModuleCat.freeMk x)) =
          (F.obj.map g) ((ModuleCat.freeDesc _) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        exact (ha V.unop U.unop g.unop x.down).symm }
  refine ⟨((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).symm η,
    fun U x => ?_⟩
  have h := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ F).apply_symm_apply η
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) h) (ModuleCat.freeMk (ULift.up x))
  exact h2.trans (ModuleCat.freeDesc_apply _ _)

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
    (ModuleCat.freeMk (ULift.up x))
  refine h.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom (ModuleCat.free_map_apply _ _)

theorem freeGen_map {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))) (ModuleCat.freeMk (ULift.up x))
  refine h.symm.trans ?_
  exact congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom (ModuleCat.free_map_apply _ _)

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

def mapHom (F G : Shv R) {U : Scheme.{0}} (x : Sec F U) : (F ⟶ G) →+ Sec G U :=
  AddMonoidHom.mk' (fun φ => Sec.map φ x) (fun _ _ => rfl)

theorem isZero_chains (E : Spc) (p : ℤ) (hp : 0 < p) : IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p (fun i hi => ?_)
  change -(i : ℤ) = p at hi
  omega

theorem chains_d (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h1 : ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv :=
    HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl
  have h2 : ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p
  rw [h1, Iso.inv_hom_id_assoc]
  exact congrArg (· ≫ (chainsXIso R E p).inv) h2

theorem chains_map {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  have h1 : ((chains R).map f).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ ((chainsN R).map f).f p ≫ (chainsXIso R E' p).inv :=
    HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1, Iso.inv_hom_id_assoc]
  rfl

variable {E : Spc} {I : Cx R} {n : ℤ}

theorem ev_def (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    _root_.GlobalTheory.EtC.ev (R := R) α p s h U x = Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl

theorem ev_ext (α β : Cochain ((chains R).obj E) I n) (h : ∀ p s h U x, _root_.GlobalTheory.EtC.ev (R := R) α p s h U x = _root_.GlobalTheory.EtC.ev (R := R) β p s h U x) : α = β := by
  ext p s hs : 1
  by_cases hp : p ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E k).inv]
    exact free_ext _ _ (fun U x => h k s hs U x)
  · exact (isZero_chains E p (by omega)).eq_of_src _ _

theorem ev_exists (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, _root_.GlobalTheory.EtC.ev (R := R) α p s h U x = a p s h U x := by
  have key : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
      Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ) (freeGen R _ U x) =
        a p j (hp ▸ hij) U x := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U x
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using key
  refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
  have := hφ _ _ h p rfl U x
  rw [eqToHom_refl, Category.id_comp] at this
  exact this

theorem ev_res (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sx E p U) : Sec.res g (_root_.GlobalTheory.EtC.ev (R := R) α p s h U x) = _root_.GlobalTheory.EtC.ev (R := R) α p s h V (x.res g) := by
  rw [ev_def, map_res, freeGen_res]
  rfl

theorem ev_add (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    _root_.GlobalTheory.EtC.ev (R := R) (a + b) p s h U x = _root_.GlobalTheory.EtC.ev (R := R) a p s h U x + _root_.GlobalTheory.EtC.ev (R := R) b p s h U x := by
  simp [_root_.GlobalTheory.EtC.ev, Cochain.add_v]

def evHom (I : Cx R) (n : ℤ) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun a => _root_.GlobalTheory.EtC.ev (R := R) a p s h U x) (fun a b => ev_add a b p s h U x)

theorem ev_zero (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    _root_.GlobalTheory.EtC.ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := map_zero (evHom I n p s h U x)

theorem ev_zsmul (c : ℤ) (a : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : _root_.GlobalTheory.EtC.ev (R := R) (c • a) p s h U x = c • _root_.GlobalTheory.EtC.ev (R := R) a p s h U x := map_zsmul (evHom I n p s h U x) c a

theorem ev_pull {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E' p U) :
    _root_.GlobalTheory.EtC.ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = _root_.GlobalTheory.EtC.ev (R := R) α p s h U (x.map f) := by
  rw [ev_def, ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

theorem ev_δ_zero {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (s t : ℤ)
    (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t) (x : Sx E 0 U) :
    _root_.GlobalTheory.EtC.ev (R := R) (δ n m α) 0 t ht U x = Sec.map (I.d s t) (_root_.GlobalTheory.EtC.ev (R := R) α 0 s hs U x) := by
  rw [ev_def, δ_v n m hm α _ t ht s 1 (by omega) (by simp),
    (isZero_chains E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0, zero_comp, smul_zero, add_zero]
  rfl

theorem ev_δ_succ {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
    _root_.GlobalTheory.EtC.ev (R := R) (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (_root_.GlobalTheory.EtC.ev (R := R) α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • _root_.GlobalTheory.EtC.ev (R := R) α p t (by omega) U (x.face i) := by
  rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add, Units.smul_def,
    Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _), chains_d, Category.assoc, Preadditive.sum_comp]
  refine (map_add (mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zsmul, map_sum, Units.smul_def]
  refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  rw [Preadditive.zsmul_comp, map_zsmul]
  congr 1
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
  rw [freeGen_map]
  rfl

end GlobalTheory.EtC.CupSpec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel
open scoped NNReal

namespace GlobalTheory.LGrp.SatakeCompare

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem isSubquotient_smInd_congr {G V W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {H H' : Subgroup G} (h : H = H') (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H), σ ⟨g, hg⟩ = σ' ⟨g, h ▸ hg⟩) (π : Representation ℂ G V) :
    _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H σ) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H' σ') := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g g.2
  rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem blk_points (n : Type) (j : n) :
    _root_.GlobalTheory.SmGL.blk (_root_.GlobalTheory.SmGL.points n) j = j := rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_Q_eq_parab_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).Q =
      _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  simp only [_root_.GlobalTheory.SmGL.mem_parab, blk_points]
  exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_p_apply_eq_diag (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) (i : n) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).p q i : kˣ) : k) = (q : GL n k) i i := rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem leviProj_points_eq_leviTorus_borel_p (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q)
    (hq : (q : GL n k) ∈ _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n)) :
    _root_.GlobalTheory.SmGL.leviProj k (_root_.GlobalTheory.SmGL.points n) ⟨q, hq⟩ =
      _root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q) := by
  funext a
  ext i j
  rw [_root_.GlobalTheory.SmGL.leviProj_apply]
  cases i; cases j
  simp [_root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points, borelGL_p_apply_eq_diag]

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem modulus_leviEmb_eq_smGL_modulus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} {m : α → Type} [Fintype α]
    [LinearOrder α] [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) (U : Subgroup (GL n k))
    (hU : U = _root_.GlobalTheory.SmGL.unipRad k e) (hc : IsClosed (U : Set (GL n k)))
    (g : _root_.GlobalTheory.SmGL.Levi k m) (x : Subgroup.normalizer (U : Set (GL n k)))
    (hx : (x : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g) :
    ((_root_.GlobalTheory.LGrp.modulus U hc x : NNReal) : ℝ) = _root_.GlobalTheory.SmGL.modulus k m g := by
  obtain ⟨x, hg⟩ := x
  simp only at hx
  subst hx
  subst hU
  letI : MeasurableSpace (_root_.GlobalTheory.SmGL.unipRad k e) := borel _
  haveI : BorelSpace (_root_.GlobalTheory.SmGL.unipRad k e) := ⟨rfl⟩
  haveI : LocallyCompactSpace (_root_.GlobalTheory.SmGL.unipRad k e) :=
    hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (_root_.GlobalTheory.SmGL.unipRad k e) := Measure.haar
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    inferInstance
  have hK : MeasurableSet (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    K.isCompact.isClosed.measurableSet
  have h1 := _root_.GlobalTheory.LGrp.modulus_measure _ hc μ ⟨_, hg⟩ (K : Set _)
  have h2 := _root_.GlobalTheory.SmGL.UnipHaar.haar_conj_eq_modulus_mul k α n m e μ g _ hK
  have hset : (_root_.GlobalTheory.LGrp.conjAut (_root_.GlobalTheory.SmGL.unipRad k e) ⟨_, hg⟩) '' (K : Set _) =
      {u : _root_.GlobalTheory.SmGL.unipRad k e | ∃ s ∈ (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)),
        (u : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g * (s : GL n k) *
          (_root_.GlobalTheory.SmGL.leviEmb k e g)⁻¹} := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, _root_.GlobalTheory.LGrp.conjAut_coe _ _ _⟩
    · rintro ⟨s, hs, hu⟩
      exact ⟨s, hs, Subtype.ext ((_root_.GlobalTheory.LGrp.conjAut_coe _ _ _).trans hu.symm)⟩
  rw [hset, h2] at h1
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h3 := (ENNReal.mul_left_inj hpos hfin).1 h1
  rw [← ENNReal.ofReal_coe_nnreal] at h3
  exact ((ENNReal.ofReal_eq_ofReal_iff (_root_.GlobalTheory.SmGL.modulus_pos k g).le
    (NNReal.coe_nonneg _)).1 h3).symm

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_U_eq_unipRad_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).U = _root_.GlobalTheory.SmGL.unipRad k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  rw [_root_.GlobalTheory.LGrp.LeviDatum.mem_U,
    _root_.GlobalTheory.SmGL.mem_unipRad, ← borelGL_Q_eq_parab_points]
  constructor
  · rintro ⟨hQ, hp⟩
    refine ⟨hQ, fun a i j => ?_⟩
    have h := congrArg (fun u : kˣ => (u : k)) (congrFun hp a)
    simp only [borelGL_p_apply_eq_diag, Pi.one_apply, Units.val_one] at h
    cases i; cases j
    simpa using h
  · rintro ⟨hQ, hd⟩
    refine ⟨hQ, funext fun a => Units.ext ?_⟩
    rw [borelGL_p_apply_eq_diag]
    simpa using hd a () ()

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_s_eq_leviEmb_points_leviTorus (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (t : n → kˣ) :
    (_root_.GlobalTheory.LGrp.borelGL k n).s t =
      _root_.GlobalTheory.SmGL.leviEmb k (_root_.GlobalTheory.SmGL.points n)
        (_root_.GlobalTheory.SmGL.leviTorus k n t) := by
  ext i j
  change ((_root_.GlobalTheory.LGrp.diagHom k n t : GL n k) : Matrix n n k) i j = _
  rw [_root_.GlobalTheory.LGrp.diagHom_val]
  simp [_root_.GlobalTheory.SmGL.leviEmb, _root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points]
  by_cases h : i = j <;> simp [h]

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).deltaHalf q : ℂˣ) : ℂ) =
      ((_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : n => Unit)
        (_root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q)) : ℂˣ) : ℂ) := by
  rw [_root_.GlobalTheory.LGrp.LeviDatum.deltaHalf_coe, _root_.GlobalTheory.SmGL.val_deltaHalf,
    _root_.GlobalTheory.LGrp.LeviDatum.delta_apply,
    modulus_leviEmb_eq_smGL_modulus k (_root_.GlobalTheory.SmGL.points n) _
      (borelGL_U_eq_unipRad_points k n) _ _ _ (borelGL_s_eq_leviEmb_points_leviTorus k n _)]


open MeasureTheory ValuativeRel in
open scoped NNReal in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] in
theorem _root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (α : n → ℂˣ) :
    _root_.GlobalTheory.LGrp.IsSubquot π (_root_.GlobalTheory.LGrp.psGL k α) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π
        (_root_.GlobalTheory.SmGL.prinSeries fun i => _root_.GlobalTheory.SmGL.unrChar k (α i)) := by
  change _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.LGrp.psGL k α) ↔ _
  unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd _root_.GlobalTheory.LGrp.LeviDatum.nIndQ
  unfold _root_.GlobalTheory.SmGL.prinSeries _root_.GlobalTheory.SmGL.indB _root_.GlobalTheory.SmGL.parInd
  refine isSubquotient_smInd_congr (borelGL_Q_eq_parab_points k n) _ _ (fun g hg => ?_) π
  refine LinearMap.ext fun z => ?_
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.LGrp.twist_apply,
    _root_.GlobalTheory.LGrp.charRep_apply, _root_.GlobalTheory.SmGL.twist_apply,
    _root_.GlobalTheory.SmGL.ofChar_apply]
  rw [leviProj_points_eq_leviTorus_borel_p k n ⟨g, hg⟩, borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus]
  simp [_root_.GlobalTheory.SmGL.torusChar_apply, _root_.GlobalTheory.LGrp.unrTorus_apply,
    _root_.GlobalTheory.LGrp.unrChar_eq]


open MeasureTheory ValuativeRel in
open scoped NNReal in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] in
theorem _root_.GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n V : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (S : Multiset ℂˣ), _root_.GlobalTheory.LGrp.HasSatakeGL π S ↔
      ∃ α : n → ℂˣ, Finset.univ.val.map α = S ∧ _root_.GlobalTheory.SmGL.HasSatake π α := by
  intro k _ _ _ _ n V _ _ _ _ _ π S
  unfold _root_.GlobalTheory.LGrp.HasSatakeGL _root_.GlobalTheory.LGrp.InUPSGL _root_.GlobalTheory.SmGL.HasSatake
    _root_.GlobalTheory.SmGL.IsSpherical _root_.GlobalTheory.LGrp.IsIrrSmooth
  rw [_root_.GlobalTheory.LGrp.isSpherical_iff]
  constructor
  · rintro ⟨⟨α, hα, ⟨-, hirr⟩, hsub⟩, hsph⟩
    exact ⟨α, hα, hirr, hsph, (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).1 hsub⟩
  · rintro ⟨α, hα, hirr, hsph, hsub⟩
    have hsub' := (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).2 hsub
    refine ⟨⟨α, hα, ⟨?_, hirr⟩, hsub'⟩, hsph⟩
    refine _root_.GlobalTheory.SmGL.IsSubquotient.isSmooth hsub' ?_
    unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd
    exact _root_.GlobalTheory.LGrp.LeviDatum.nInd_isSmooth _ _

end GlobalTheory.LGrp.SatakeCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

def ClosureEtaleAt (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (P : Ideal R) [P.IsPrime] : Prop :=
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  Algebra.Etale (Localization.AtPrime P)
    (TensorProduct R (Localization.AtPrime P) (GlobalTheory.KeyOriginNoeth.closure A R D))

theorem good_iff_etaleAt (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) :
    GlobalTheory.KeyOriginNoeth.Good A R D ρ ↔
      ((∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
          ClosureEtaleAt A R D P) ∧ PointAtZero A R D ρ) := Iff.rfl

end GlobalTheory.KeyOriginEnlarge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
open ValuativeRel

noncomputable section

namespace GlobalTheory.UnfoldLoss

open GlobalTheory.SplitFlip GlobalTheory.FunObj

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def varLat (G : Grid k) (ϖ : kˣ) (n : ℕ) : AddSubgroup (Vars G) where
  carrier := {e | ∀ j r, valuation k (e j r) ≤ valuation k ((ϖ ^ n : kˣ) : k)}
  zero_mem' := fun j r => by
    show valuation k 0 ≤ _
    simp
  add_mem' := fun {a b} ha hb j r => (Valuation.map_add _ _ _).trans (max_le (ha j r) (hb j r))
  neg_mem' := fun {a} ha j r => by
    show valuation k (-(a j r)) ≤ _
    rw [Valuation.map_neg]
    exact ha j r

def varCount (G : Grid k) : ℕ :=
  ∑ j : Fin (G.m - 1), Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)))

end GlobalTheory.UnfoldLoss
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureAdditiveAutomorphismScale
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory

namespace GlobalTheory.HaarScaleMatrix


open scoped Matrix in
open MeasureTheory in
theorem _root_.GlobalTheory.HaarScaleMatrix.secondCountable_of_localField (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SecondCountableTopology k :=
  _root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field.1

end GlobalTheory.HaarScaleMatrix
end
