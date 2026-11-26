module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicProperties
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicProperties
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem hl_basic : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O), D.HL.Normal ∧ IsOpen (D.HL : Set (GQ l)) ∧ IsOpenEmbedding D.HL.subtype ∧ (∀ s ∈ D.HL, s ∈ Iq l → D.Ψ s = cycA l l O s ^ D.e) ∧ GlobalTheory.OrdLoc.IsInertiaInfiniteCyclotomic D (GlobalTheory.OrdLoc.s0 D) := by
  intro l _ O _ _ _ D
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    rw [this]
    haveI := D.Kv.2
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have ho : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  have hex : ∃ s, IsInertiaInfiniteCyclotomic D s := by
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := ((cycInertia l).2 D.HL ho).2
    exact ⟨s, hs1, hs2, hs⟩
  refine ⟨inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal, ho, ho.isOpenEmbedding_subtypeVal, fun s hs hi => ?_,
    Classical.epsilon_spec hex⟩
  have ht : D.τ s = 1 := hs.2
  rw [D.Ψ_I s hi, ht, mul_one]

end GlobalTheory.OrdLoc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisSubgroupL_basic_properties : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O), D.HL.Normal ∧ IsOpen (D.HL : Set (GQ l)) ∧ IsOpenEmbedding D.HL.subtype ∧ (∀ s ∈ D.HL, s ∈ Iq l → D.Ψ s = cycA l l O s ^ D.e) ∧ GlobalTheory.OrdLoc.IsInertiaInfiniteCyclotomic D (GlobalTheory.OrdLoc.s0 D) := by
  first | exact @GlobalTheory.OrdLoc.hl_basic | exact GlobalTheory.OrdLoc.hl_basic | (intros; apply GlobalTheory.OrdLoc.hl_basic <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsMapAlgHomStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem push_mat_eq_mat_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (s : GQ l) : (push f r s).mat = (r s).mat.map f := by
  rfl
private theorem sh_push_eq_sh_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (a : Fin 3) (s : GQ l) : D.sh (push f r) a s = (D.sh r a s).map f := by
  ext i j
  simp only [Dat3.sh, Matrix.sub_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, push_mat_eq_mat_map, map_sub]
  split_ifs <;> simp
private theorem tr_push_algHom_eq_map_tr {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (a : Fin 3) : D.tr (push f r) a = f (D.tr r a) := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dat3.tr, sh_push_eq_sh_map, push_mat_eq_mat_map, h, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
private theorem map_dd_eq_dd_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (a : Fin 3) : f (D.dd r a) = D.dd (push f r) a := by
  simp only [Dat3.dd, tr_push_algHom_eq_map_tr, map_sub, map_mul, AlgHom.commutes]
private theorem map_coeff_charpoly_sub_prod_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (s : GQ l) (i : ℕ) : f (((r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) = (((push f r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) := by
  have h1 : (push f r s).mat.charpoly = (r s).mat.charpoly.map (f : C →+* C') := by
    rw [push_mat_eq_mat_map]
    exact Matrix.charpoly_map _ _
  have h2 : ∀ a : Fin 3, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))) = (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))).map (f : C →+* C') := by
    intro a
    simp
  rw [h1, Finset.prod_congr rfl (fun a _ => h2 a), ← Polynomial.map_prod, ← Polynomial.map_sub, Polynomial.coeff_map]
  rfl
private theorem map_sh_triple_prod_apply_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (s : Fin 3 → GQ l) (i j : Fin 3) : f ((D.sh r 0 (s 0) * D.sh r 1 (s 1) * D.sh r 2 (s 2)) i j) = (D.sh (push f r) 0 (s 0) * D.sh (push f r) 1 (s 1) * D.sh (push f r) 2 (s 2)) i j := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm
  simp only [sh_push_eq_sh_map, h, Matrix.map_apply]

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryIdeal_saturators_map_algHom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)), (GlobalTheory.OrdLoc.ordIdeal D r).map (f : C →+* C') = GlobalTheory.OrdLoc.ordIdeal D (push f r) ∧ (∀ a, f (GlobalTheory.OrdLoc.dd D r a) = GlobalTheory.OrdLoc.dd D (push f r) a) ∧ f (GlobalTheory.OrdLoc.del D r) = GlobalTheory.OrdLoc.del D (push f r) := by
  intro l _ O _ _ _ D C C' _ _ _ _ f r
  refine ⟨?_, fun a => map_dd_eq_dd_push D f r a, ?_⟩
  · simp only [Dat3.ordIdeal]
    rw [Ideal.map_span, Set.image_union]
    congr 2
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, rfl⟩, rfl⟩
        exact ⟨s, hs, i, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
      · rintro ⟨s, hs, i, rfl⟩
        exact ⟨_, ⟨s, hs, i, rfl⟩, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, j, rfl⟩, rfl⟩
        exact ⟨s, hs, i, j, map_sh_triple_prod_apply_eq_push D f r s i j⟩
      · rintro ⟨s, hs, i, j, rfl⟩
        exact ⟨_, ⟨s, hs, i, j, rfl⟩, map_sh_triple_prod_apply_eq_push D f r s i j⟩
  · simp only [Dat3.del, map_mul, map_natCast, map_dd_eq_dd_push]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobenius
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobenius
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]

theorem hl_normal' (D : Dat3 l O) : D.HL.Normal := by
  unfold Dat3.HL; infer_instance

theorem hl_isOpen' (D : Dat3 l O) : IsOpen (D.HL : Set (GQ l)) := by
  have e : (D.η.ker : Set (GQ l)) = (D.Kv.1.fixingSubgroup : Set (GQ l)) := by
    ext g; exact D.η_ker g
  have h1 : IsOpen (D.η.ker : Set (GQ l)) := by
    rw [e]; haveI := D.Kv.2; exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  exact h1.inter D.τ_open

theorem finiteIndex_of_open' (H : OpenSubgroup (GQ l)) : (H : Subgroup (GQ l)).FiniteIndex := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_isFr (D : Dat3 l O) : ∃ σ, IsFr D σ := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  haveI hHn : D.HL.Normal := hl_normal' D
  have hHo : IsOpen (D.HL : Set (GQ l)) := hl_isOpen' D
  obtain ⟨hIn, -, -, ⟨σ₀, hσ₀⟩, -⟩ := iqBasic l
  haveI : D.HL.FiniteIndex := finiteIndex_of_open' ⟨D.HL, hHo⟩
  set N : Subgroup (GQ l) := D.HL ⊔ Iq l with hN
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  haveI : N.Normal := Subgroup.sup_normal _ _
  set q : GQ l ⧸ N := (σ₀ : GQ l ⧸ N)
  set m := orderOf q with hm
  have hm1 : 1 ≤ m := orderOf_pos q
  have hmN : σ₀ ^ m ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one q
  obtain ⟨h, hh, i₀, hi₀, hhi⟩ := Subgroup.mem_sup_of_normal_right.1 hmN
  let φ := QuotientGroup.mk' (Iq l)
  have hφ : ∀ {x}, φ x = 1 ↔ x ∈ Iq l := fun {x} => QuotientGroup.eq_one_iff x
  have hφm : φ σ₀ ^ m = φ h := by
    rw [← map_pow, ← hhi, map_mul, hφ.2 hi₀, mul_one]
  refine ⟨h, ⟨hh, ?_⟩, σ₀, m, hσ₀, hm1, ?_⟩
  ·
    rw [eq_top_iff]
    intro g _
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    rw [mem_closure_iff]
    intro U hU hgU
    have hdense := frobDense σ₀ hσ₀
    have hV : IsOpen (D.HL.subtype '' U) := (hHo.isOpenEmbedding_subtypeVal).isOpenMap U hU
    have hcl : (D.HL.subtype g) ∈ closure ((Iq l ⊔ Subgroup.zpowers σ₀ : Subgroup (GQ l)) : Set (GQ l)) := by
      rw [← Subgroup.topologicalClosure_coe, hdense]; trivial
    obtain ⟨x, ⟨u, huU, rfl⟩, hxT⟩ := mem_closure_iff.1 hcl _ hV ⟨g, hgU, rfl⟩
    obtain ⟨i, hi, z, hz, hiz⟩ := Subgroup.mem_sup_of_normal_left.1 hxT
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    change i * σ₀ ^ k = (u : GQ l) at hiz
    have hkN : σ₀ ^ k ∈ N := by
      have : σ₀ ^ k = i⁻¹ * (u : GQ l) := by rw [← hiz]; group
      rw [this]
      exact N.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hi)) (Subgroup.mem_sup_left u.2)
    have hdvd : (m : ℤ) ∣ k := by
      rw [hm, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]; exact hkN
    obtain ⟨j, rfl⟩ := hdvd
    have hφu : φ (u : GQ l) = φ h ^ j := by
      rw [← hiz, map_mul, hφ.2 hi, one_mul, map_zpow, zpow_mul, zpow_natCast, hφm]
    have hy : (u : GQ l) * h ^ (-j) ∈ Iq l := by
      rw [← hφ, map_mul, map_zpow, hφu, zpow_neg, mul_inv_cancel]
    refine ⟨u, huU, ?_⟩
    have e : u = (⟨(u : GQ l) * h ^ (-j), D.HL.mul_mem u.2 (D.HL.zpow_mem hh _)⟩ : ↥D.HL) * (⟨h, hh⟩ : ↥D.HL) ^ j := by
      ext; simp
    rw [SetLike.mem_coe, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
  · rw [← hhi]; simpa using Subgroup.inv_mem _ hi₀

theorem fr_isFr : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O),
    GlobalTheory.OrdLoc.IsFr D (GlobalTheory.OrdLoc.fr D) := by
  intro l _ O _ _ _ D
  exact Classical.epsilon_spec (exists_isFr D)

end GlobalTheory.OrdLoc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobeniusStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenFrobenius_isFrobenius : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O), GlobalTheory.OrdLoc.IsFr D (GlobalTheory.OrdLoc.fr D) := by
  first | exact @GlobalTheory.OrdLoc.fr_isFr | exact GlobalTheory.OrdLoc.fr_isFr | (intros; apply GlobalTheory.OrdLoc.fr_isFr <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.NilpotentTwistStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem sh_s0_eq_diagonal_psi_sub_psi {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (b : Fin 3) : D.sh r b D.s0 = Matrix.diagonal (fun c => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ c D.s0) - algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0)) := by
  rw [Dat3.sh, h, Matrix.scalar_apply, Matrix.diagonal_sub]
private theorem tr_lemma_2 {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (a : Fin 3) : D.tr r a = algebraMap O C (D.cc a) * (r D.fr).mat a a := by
  rw [Dat3.tr, sh_s0_eq_diagonal_psi_sub_psi D r h, sh_s0_eq_diagonal_psi_sub_psi D r h, Matrix.diagonal_mul_diagonal, Matrix.trace, Fin.sum_univ_three]
  simp only [Matrix.diag, Matrix.diagonal_mul, Dat3.cc, map_mul, map_sub]
  fin_cases a <;> simp <;> ring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_derivative_entry_formula : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)), (r (GlobalTheory.OrdLoc.s0 D)).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (GlobalTheory.OrdLoc.s0 D))) → ∀ a : Fin 3, GlobalTheory.OrdLoc.dd D r a = algebraMap O C (GlobalTheory.OrdLoc.cc D a * GlobalTheory.OrdLoc.cc D (a + 1)) * ((r (GlobalTheory.OrdLoc.fr D)).mat a a - algebraMap O C ((cycA l l O (GlobalTheory.OrdLoc.fr D) : Oˣ) : O) * (r (GlobalTheory.OrdLoc.fr D)).mat (a + 1) (a + 1)) := by
  intro l _ O _ _ _ D C _ _ r h a
  simp only [Dat3.dd, tr_lemma_2 D r h, map_mul]
  ring
end
