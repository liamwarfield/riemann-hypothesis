module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ContinuousCj

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.SemisimpleAdjoint.IsSemisimpleOfMem
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Desc.SLF.CRAdj

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem isSemisimple_of_mem (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) {a : Matrix (Fin n) (Fin n) k}
    (ha : a ∈ Z) : Module.End.IsSemisimple (Matrix.toLin' a) := by
  haveI : IsReduced Z := hZ.2
  let a' : Z := ⟨a, ha⟩
  have hint : IsIntegral k a' := .of_finite k a'
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    ((minpoly.isRadical k a').squarefree (minpoly.ne_zero hint)) ?_
  have h1 : aeval a (minpoly k a') = 0 := by
    have := congrArg (Subalgebra.val Z) (minpoly.aeval k a')
    rwa [← Polynomial.aeval_algHom_apply, map_zero] at this
  have e : Matrix.toLin' a = (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _) a := rfl
  rw [e, Polynomial.aeval_algHom_apply, h1, map_zero]

theorem comm_gen (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) {s : Matrix (Fin n) (Fin n) k}
    (hs : s ∈ Bz Z) : ∀ a ∈ insert s (Z : Set (Matrix (Fin n) (Fin n) k)),
      ∀ b ∈ insert s (Z : Set (Matrix (Fin n) (Fin n) k)), a * b = b * a := by
  have hs' : ∀ a ∈ Z, a * s = s * a := hs
  intro a ha b hb
  rcases Set.mem_insert_iff.mp ha with h1 | h1 <;> rcases Set.mem_insert_iff.mp hb with h2 | h2
  · rw [h1, h2]
  · rw [h1]
    exact (hs' b h2).symm
  · rw [h2]
    exact hs' a h1
  · exact hZ.1 a h1 b h2

theorem adj_comm (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) {s : Matrix (Fin n) (Fin n) k}
    (hs : s ∈ Bz Z) : ∀ a ∈ adj Z s, ∀ b ∈ adj Z s, a * b = b * a := by
  intro a ha b hb
  have h1 : ∀ c ∈ insert s (Z : Set (Matrix (Fin n) (Fin n) k)), Commute c b := fun c hc =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb (fun d hd => comm_gen Z hZ hs c hc d hd)
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (fun c hc => (h1 c hc).symm)).symm.eq

private theorem lin_comm_lemma {a b : Matrix (Fin n) (Fin n) k} (h : a * b = b * a) :
    Commute (Matrix.toLin' a) (Matrix.toLin' b) :=
  (show Commute a b from h).map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _)

theorem cr_adj [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (s : Matrix (Fin n) (Fin n) k)
    (hs : s ∈ Bz Z) (hss : Module.End.IsSemisimple (Matrix.toLin' s)) : CR (adj Z s) := by
  have hsem : ∀ x (hx : x ∈ adj Z s), Module.End.IsSemisimple (Matrix.toLin' x) := by
    intro x hx
    change x ∈ Algebra.adjoin k (insert s (Z : Set (Matrix (Fin n) (Fin n) k))) at hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact hss
      · exact isSemisimple_of_mem Z hZ hy
    | algebraMap r =>
      rw [show Matrix.toLin' (algebraMap k (Matrix (Fin n) (Fin n) k) r) =
          algebraMap k (Module.End k (Fin n → k)) r from
        (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _).commutes r]
      exact Module.End.IsSemisimple.of_mem_adjoin_pair (Commute.refl _) hss hss
        (Subalgebra.algebraMap_mem _ r)
    | add y z hy hz ihy ihz =>
      rw [map_add (f := _)]
      exact Module.End.IsSemisimple.add_of_commute (lin_comm_lemma (adj_comm Z hZ hs y hy z hz)) ihy ihz
    | mul y z hy hz ihy ihz =>
      rw [show Matrix.toLin' (y * z) = Matrix.toLin' y * Matrix.toLin' z from
        map_mul (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _) y z]
      exact Module.End.IsSemisimple.mul_of_commute (lin_comm_lemma (adj_comm Z hZ hs y hy z hz)) ihy ihz
  refine ⟨adj_comm Z hZ hs, ⟨fun x hx => ?_⟩⟩
  have hN : IsNilpotent (Matrix.toLin' (x : Matrix (Fin n) (Fin n) k)) :=
    (hx.map (adj Z s).val).map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _)
  have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hN (hsem x x.2)
  apply Subtype.ext
  have h2 : (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _) (x : Matrix (Fin n) (Fin n) k) = 0 := h0
  simpa using h2

end PositivityTheory.RgUd.T.Desc.SLF.CRAdj
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ExistsConjEqSemisimple
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.T2SpaceCentralizerGroup
noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem t2k : T2Space k := Asm.t2

theorem tdk : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField

theorem sck : SecondCountableTopology k := (GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).1

theorem continuous_aevalM (P : k[X]) : Continuous fun x : Matrix (Fin n) (Fin n) k => aeval x P := by
  have : T2Space k := t2k
  simp_rw [aeval_eq_sum_range]
  exact continuous_finsetSum _ fun i _ => (continuous_pow i).const_smul (P.coeff i)

theorem isClosed_Tset {F : Set (Matrix (Fin n) (Fin n) k)} (hF : IsClosed F) (P : k[X]) : IsClosed (Tset F P) := by
  have : T2Space k := t2k
  exact hF.inter (isClosed_eq (continuous_aevalM P) continuous_id)

instance t2Space_centralizer_group (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : T2Space (GzS Z) := by
  have : T2Space k := t2k
  infer_instance

instance gzs_td (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : TotallyDisconnectedSpace (GzS Z) := by
  infer_instance

instance gzs_sc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : SecondCountableTopology (GzS Z) := by
  have : SecondCountableTopology (GL (Fin n) k) := GlobalTheory.SplitFlip.secondCountable_GL
  exact TopologicalSpace.Subtype.secondCountableTopology _

instance gzs_sig (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : SigmaCompactSpace (GzS Z) := by
  infer_instance

end PositivityTheory.RgUd.T.Desc.SLF
end
end

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

section Hyp

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {F : Set (Matrix (Fin n) (Fin n) k)} {P : k[X]}
  {s : Matrix (Fin n) (Fin n) k}
  (hFinv : ∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F)
  (hP : ∀ x ∈ F, aeval x P ∈ F ∧ Module.End.IsSemisimple (Matrix.toLin' (aeval x P)) ∧ IsNilpotent (x - aeval x P) ∧
    ∃ g ∈ Gz Z, g.val * aeval x P * g⁻¹.val = s)

include hP in
theorem P_idem [CharZero k] {x} (hx : x ∈ F) : aeval (aeval x P) P = aeval x P := by
  set y := aeval x P with hydef
  obtain ⟨hyF, hyS, -, -⟩ := hP x hx
  obtain ⟨-, hzS, hzN, -⟩ := hP y hyF
  have e : ∀ M : Matrix (Fin n) (Fin n) k, Matrix.toLinAlgEquiv' M = Matrix.toLin' M := fun M => rfl
  have hc : Commute y (aeval y P) := by
    have := (Commute.all (X : k[X]) P).map (aeval y)
    rwa [aeval_X] at this
  have hc' : Commute (Matrix.toLin' y) (Matrix.toLin' (aeval y P)) := by
    have := hc.map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _)
    rwa [e, e] at this
  have hS : Module.End.IsSemisimple (Matrix.toLin' (y - aeval y P)) := by
    rw [map_sub]
    exact Module.End.IsSemisimple.sub_of_commute hc' hyS hzS
  have hN : IsNilpotent (Matrix.toLin' (y - aeval y P)) := by
    rw [← e]
    exact hzN.map _
  have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hN hS
  rw [← e, map_eq_zero_iff _ (AlgEquiv.injective _), sub_eq_zero] at h0
  exact h0.symm

include hP in
theorem P_mem_Tset [CharZero k] {x} (hx : x ∈ F) : aeval x P ∈ Tset F P := ⟨(hP x hx).1, P_idem hP hx⟩

include hP in
theorem exists_conj_eq_semisimple {x} (hx : x ∈ Tset F P) : ∃ g ∈ Gz Z, cj g x = s := by
  obtain ⟨hxF, hxP⟩ := hx
  obtain ⟨-, -, -, g, hg, hgs⟩ := hP x hxF
  rw [hxP] at hgs
  exact ⟨g, hg, hgs⟩

theorem continuousSMul_actT : @ContinuousSMul (GzS Z) (Tset F P) (actT hFinv).toSMul _ _ := by
  refine @ContinuousSMul.mk _ _ (actT hFinv).toSMul _ _ ?_
  exact (((Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_mul
    (continuous_subtype_val.comp continuous_snd)).matrix_mul
    (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst))).subtype_mk _

include hP in
theorem isPretransitive_actT (hsT : s ∈ Tset F P) : @MulAction.IsPretransitive (GzS Z) (Tset F P) (actT hFinv).toSMul := by
  refine @MulAction.IsPretransitive.mk _ _ (actT hFinv).toSMul ?_
  intro x y
  obtain ⟨a, ha, hax⟩ := exists_conj_eq_semisimple hP x.2
  obtain ⟨b, hb, hby⟩ := exists_conj_eq_semisimple hP y.2
  refine ⟨⟨b⁻¹ * a, (GzS Z).mul_mem ((GzS Z).inv_mem hb) ha⟩, Subtype.ext ?_⟩
  show cj (b⁻¹ * a) x.1 = y.1
  simp only [cj] at hax hby ⊢
  simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  calc (b⁻¹ : GL (Fin n) k).val * a.val * x.1 * (a⁻¹.val * b.val)
      = (b⁻¹ : GL (Fin n) k).val * (a.val * x.1 * a⁻¹.val) * b.val := by
        simp only [Matrix.mul_assoc]
    _ = (b⁻¹ : GL (Fin n) k).val * (b.val * y.1 * b⁻¹.val) * b.val := by rw [hax, hby]
    _ = y.1 := by simp [Matrix.mul_assoc]

end Hyp

end PositivityTheory.RgUd.T.Desc.SLF
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsUnimodOfEquiv
noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace PositivityTheory.RgUd.T.Desc.SLF

theorem isUnimod_of_equiv {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] (φ : G₁ ≃ₜ* G₂)
    (h : PositivityTheory.PfBern.Frob.IsUnimod G₂) : PositivityTheory.PfBern.Frob.IsUnimod G₁ := by
  intro g
  have hg : modularCharacterFun (φ g) = 1 := h (φ g)
  show modularCharacterFun g = 1
  borelize G₁ G₂
  let μ₂ : Measure G₂ := haar
  have hme : MeasurableEmbedding (φ.symm : G₂ → G₁) := φ.symm.toHomeomorph.measurableEmbedding
  let μ₁ : Measure G₁ := map (φ.symm : G₂ → G₁) μ₂
  haveI : IsHaarMeasure μ₁ := ContinuousMulEquiv.isHaarMeasure_map μ₂ φ.symm
  rw [modularCharacterFun_eq_haarScalarFactor μ₁ g]
  rw [modularCharacterFun_eq_haarScalarFactor μ₂ (φ g)] at hg
  obtain ⟨f, hfc, hf0, hf1⟩ := exists_continuous_nonneg_pos (1 : G₁)
  let f₂ : G₂ → ℝ := fun y => f (φ.symm y)
  have hf₂c : Continuous f₂ := f.continuous.comp φ.symm.continuous
  have hf₂s : HasCompactSupport f₂ := hfc.comp_homeomorph φ.symm.toHomeomorph
  have I1 : ∫ x, f x ∂μ₁ = ∫ y, f₂ y ∂μ₂ := hme.integral_map _
  have I2 : ∫ x, f x ∂(map (· * g) μ₁) = ∫ y, f₂ y ∂(map (· * φ g) μ₂) := by
    rw [integral_map (measurable_mul_const g).aemeasurable f.continuous.aestronglyMeasurable,
      show μ₁ = map (φ.symm : G₂ → G₁) μ₂ from rfl, hme.integral_map,
      integral_map (measurable_mul_const (φ g)).aemeasurable hf₂c.aestronglyMeasurable]
    congr 1
    funext x
    simp [f₂, map_mul]
  have hpos : ∫ x, f x ∂μ₁ ≠ 0 :=
    (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hf1).ne'
  have hpos₂ : ∫ y, f₂ y ∂μ₂ ≠ 0 := by
    rw [← I1]
    exact hpos
  have hg' : ((haarScalarFactor (map (· * φ g) μ₂) μ₂ : NNReal) : ℝ) = 1 := by
    rw [hg]
    rfl
  rw [haarScalarFactor_eq_integral_div _ _ hf₂c hf₂s hpos₂] at hg'
  apply NNReal.coe_injective
  rw [haarScalarFactor_eq_integral_div _ _ f.continuous hfc hpos, I2, I1, hg', NNReal.coe_one]

end PositivityTheory.RgUd.T.Desc.SLF
end
end

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem centralizer_le_of {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {s x : Matrix (Fin n) (Fin n) k}
    (hx : ∀ a ∈ Z, a * x = x * a) (hs : s * x = x * s) :
    adj Z s ≤ Subalgebra.centralizer k ({x} : Set (Matrix (Fin n) (Fin n) k)) := by
  apply Algebra.adjoin_le
  intro a ha
  rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · exact hs.symm
  · exact (hx a ha).symm

theorem mem_Bz_adj {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {s x : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Bz Z) (hs : s * x = x * s) : x ∈ Bz (adj Z s) := by
  show ∀ a ∈ adj Z s, a * x = x * a
  intro a ha
  have h := centralizer_le_of hx hs ha
  rw [Subalgebra.mem_centralizer_iff] at h
  exact (h x (Set.mem_singleton x)).symm

theorem mem_Gz_adj_iff {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {s : Matrix (Fin n) (Fin n) k} {g : GL (Fin n) k} :
    g ∈ Gz (adj Z s) ↔ g ∈ Gz Z ∧ s * g.val = g.val * s := by
  simp only [Gz, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha)),
      h s (Algebra.subset_adjoin (Set.mem_insert _ _))⟩
  · rintro ⟨h1, h2⟩ a ha
    have h := centralizer_le_of (x := (g : Matrix (Fin n) (Fin n) k)) h1 h2 ha
    rw [Subalgebra.mem_centralizer_iff] at h
    exact (h _ (Set.mem_singleton _)).symm

def Xs (F : Set (Matrix (Fin n) (Fin n) k)) : Set (Sp k n) := F ×ˢ Set.univ

section Act

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {F : Set (Matrix (Fin n) (Fin n) k)}
  (hFinv : ∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F)

include hFinv in
theorem act_mem_Xs {g : GL (Fin n) k} (hg : g ∈ Gz Z) {q : Sp k n} (hq : q ∈ Xs F) : act g q ∈ Xs F := by
  refine Set.mem_prod.mpr ⟨?_, Set.mem_univ _⟩
  exact hFinv g hg q.1 (Set.mem_prod.mp hq).1

theorem act_mul (g h : GL (Fin n) k) (q : Sp k n) : act (g * h) q = act g (act h q) := by
  simp only [act, Units.val_mul, _root_.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem act_one (q : Sp k n) : act (1 : GL (Fin n) k) q = q := by simp [act]

def actX : MulAction (GzS Z) (Xs F) where
  smul g q := ⟨act g.1 q.1, act_mem_Xs hFinv g.2 q.2⟩
  one_smul q := Subtype.ext (act_one q.1)
  mul_smul g h q := Subtype.ext (act_mul g.1 h.1 q.1)

theorem continuous_act : Continuous fun p : GL (Fin n) k × Sp k n => act p.1 p.2 := by
  unfold act
  refine Continuous.prodMk ?_ ?_
  · exact ((Units.continuous_val.comp continuous_fst).matrix_mul
      (continuous_fst.comp continuous_snd)).matrix_mul
      (Units.continuous_coe_inv.comp continuous_fst)
  · exact (Units.continuous_val.comp continuous_fst).matrix_mulVec
      (continuous_snd.comp continuous_snd)

theorem continuousSMul_actX : @ContinuousSMul (GzS Z) (Xs F) (actX hFinv).toSMul _ _ := by
  letI := actX hFinv
  refine ⟨Continuous.subtype_mk ?_ _⟩
  exact continuous_act.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))

end Act

end PositivityTheory.RgUd.T.Desc.SLF
