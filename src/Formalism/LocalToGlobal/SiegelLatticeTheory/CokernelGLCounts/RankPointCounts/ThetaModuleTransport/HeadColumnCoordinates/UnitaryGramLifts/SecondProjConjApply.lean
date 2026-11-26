module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FirstProjConjApply
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjEqFirstProj
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

section DuU

theorem firstProj_conj_eq_secondProj (x : E) : ph1 g ((M.L.cj : E →+* E) x) = ph2 g x := by
  simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem secondProj_conj_eq_firstProj (x : E) : ph2 g ((M.L.cj : E →+* E) x) = ph1 g x := by
  simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem firstProj_algebraMap (a : F) : ph1 g (algebraMap F E a) = a := by
  simp [firstProj_apply]

theorem ph2_algebraMap_eq (a : F) : ph2 g (algebraMap F E a) = a := by
  simp [secondProj_apply]

theorem firstProj_corner (a b : Fin (r + 1)) (X : E) : ph1 g (cor r a b X) = cor r a b (ph1 g X) := by
  unfold cor; split_ifs <;> simp

theorem firstProj_iotaOne_inl (hs : M.split = some g) (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    ph1 g ((iota1 hs l (Sum.inl a) : M.L.O) : E) = ph1 g (l a : E) := by
  simp [iota1, firstProj_apply]

theorem firstProj_iotaOne_inr (hs : M.split = some g) (l : Fin (r + 1) → M.R) (a : Fin (r + 1)) :
    ph1 g ((iota1 hs l (Sum.inr a) : M.L.O) : E) = (ph2 g (l a : E) - ph1 g (l a : E)) / (g.q : F) := by
  simp [iota1, firstProj_apply, secondProj_apply]

theorem firstProj_conj_iotaTwo (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g ((M.L.cj : E →+* E) ((iota2 hs l i : M.L.O) : E)) = ph1 g ((iota1 hs l i : M.L.O) : E) := by
  simp [iota2, firstProj_apply, g.e_cj, M.L.cj_cj]

theorem duU_formG_sub (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y W W' : Ix r → O) :
    formG O cj qi Z T T' Y W - formG O cj qi Z T T' Y W' =
      ∑ i, (Y i : E) * (Matrix.mulVec (gramG cj qi Z T T')⁻¹ fun j => cj (W j) - cj (W' j)) i := by
  unfold formG
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub, mul_assoc]

theorem firstProj_sum_iotaOne (hs : M.split = some g) (l : Fin (r + 1) → M.R) (c : Ix r → E) :
    ph1 g (∑ i, ((iota1 hs l i : M.L.O) : E) * c i) =
      ∑ a, ph1 g (l a : E) * ph1 g (c (Sum.inl a)) +
        ∑ a, (ph2 g (l a : E) - ph1 g (l a : E)) / (g.q : F) * ph1 g (c (Sum.inr a)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Fintype.sum_sum_type]
  simp only [map_mul, firstProj_iotaOne_inl, firstProj_iotaOne_inr]

theorem duU_sum_single1 (a : Fin (r + 1)) (x : M.R) (f : Fin (r + 1) → F) :
    ∑ b, ph1 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E) * f b = ph1 g (x : E) * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem duU_sum_single2 (a : Fin (r + 1)) (x : M.R) (f : Fin (r + 1) → F) :
    ∑ b, (ph2 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E) - ph1 g (((Pi.single a x : Fin (r + 1) → M.R) b : M.R) : E)) / (g.q : F) * f b =
      (ph2 g (x : E) - ph1 g (x : E)) / (g.q : F) * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem ph1_mem_integers_of_mem_O {y : E} (hy : y ∈ M.L.O) : ph1 g y ∈ 𝒪[F] := by
  have hidem : (g.e.symm (1, 0) : E) * g.e.symm (1, 0) = g.e.symm (1, 0) := by
    rw [← map_mul]
    simp
  have hu : y * g.e.symm (1, 0) ∈ M.L.O := M.L.O.mul_mem hy (idem_mem_O M.L hidem)
  have hw : y * g.e.symm (1, 0) + M.L.cj (y * g.e.symm (1, 0)) ∈ M.L.O :=
    M.L.O.add_mem hu (cj_mem_O M.L hu)
  have heq : y * g.e.symm (1, 0) + M.L.cj (y * g.e.symm (1, 0)) = algebraMap F E (ph1 g y) := by
    apply g.e.injective
    refine Prod.ext ?_ ?_ <;> simp [g.e_cj, firstProj_apply]
  haveI : Nontrivial E := g.e.toEquiv.nontrivial
  exact Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (heq ▸ hw)

theorem duU_c_int (hs : M.split = some g) (c : Ix r → E)
    (h : ∀ l : Fin (r + 1) → M.R, ∑ i, ((iota1 hs l i : M.L.O) : E) * c i ∈ M.L.O) :
    ∀ i, ph1 g (c i) ∈ 𝒪[F] := by
  have hq : (g.q : F) ≠ 0 := by
    intro h0
    exact g.q_irr.ne_zero (Subtype.ext h0)
  intro i
  rcases i with a | a
  · have h1 := ph1_mem_integers_of_mem_O (g := g) (h (Pi.single a 1))
    rw [firstProj_sum_iotaOne hs] at h1
    simp only [duU_sum_single1, duU_sum_single2] at h1
    simpa using h1
  · have h1 := ph1_mem_integers_of_mem_O (g := g) (h (Pi.single a (q2 hs)))
    rw [firstProj_sum_iotaOne hs] at h1
    simp only [duU_sum_single1, duU_sum_single2] at h1
    simpa [firstProj_apply, secondProj_apply, embedding_uniformizer hs, hq] using h1

theorem duU_sum_cor (a : Fin (r + 1)) (X : F) (f : Fin (r + 1) → F) :
    ∑ b, cor r a b X * f b = if a = Fin.last r then X * f (Fin.last r) else 0 := by
  unfold cor
  split_ifs with ha
  · simp [ha, ite_mul]
  · simp [ha]

theorem firstProj_zzPlus_conj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      ph2 g (Zh a b) / (g.q : F) - cor r a b (-T / (g.q : F)) := by
  unfold cor
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp [firstProj_apply, secondProj_apply, g.e_cj]

theorem secondProj_zzPlus_conj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b) =
      -(ph1 g (Zh b a) / (g.q : F)) - cor r a b (T' / (g.q : F)) := by
  unfold cor
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp [firstProj_apply, secondProj_apply, g.e_cj]

end DuU

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section DuU2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem firstProj_conj_apply (x : E) : ph1 g (M.L.cj x) = ph2 g x := firstProj_conj_eq_secondProj x

theorem duU_core (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z Zσ : M.Mat (r + 1)} (hG : GHyp M g T T' TT Zh Z Zσ)
    (hdet : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det)
    (w w' : Fin (r + 1) → M.R)
    (h : ∀ l : Fin (r + 1) → M.R,
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
          (iota1 hs l) (iota2 hs w) -
        formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
          (iota1 hs l) (iota2 hs w') ∈ M.L.O) :
    w - w' ∈ LL hs Zσ TT := by
  obtain ⟨G, hGd⟩ : ∃ G, gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') = G := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Ix r → E, (fun j => (M.L.cj : E →+* E) ((iota2 hs w j : M.L.O) : E) -
      (M.L.cj : E →+* E) ((iota2 hs w' j : M.L.O) : E)) = v := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Ix r → E, Matrix.mulVec G⁻¹ v = c := ⟨_, rfl⟩
  have hsum : ∀ l, ∑ i, ((iota1 hs l i : M.L.O) : E) * c i ∈ M.L.O := by
    intro l
    have := h l
    rw [duU_formG_sub, hGd, hv, hc] at this
    exact this
  have hint := duU_c_int hs c hsum
  have hGc : Matrix.mulVec G c = v := by
    rw [← hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hGd ▸ hdet), Matrix.one_mulVec]
  have hrow : ∀ i, ∑ j, ph1 g (G i j) * ph1 g (c j) = ph1 g (v i) := by
    intro i
    have := congrArg (ph1 g) (congrFun hGc i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at this
    exact this
  have hG11 : ∀ a b, ph1 g (G (Sum.inl a) (Sum.inl b)) = cor r a b (-T) := by
    intro a b; rw [← hGd]; simp [gramG, firstProj_corner, firstProj_algebraMap]
  have hG12 : ∀ a b, ph1 g (G (Sum.inl a) (Sum.inr b)) = (g.q : F)⁻¹ * (ph2 g (Zh a b) + cor r a b T) := by
    intro a b; rw [← hGd]; simp [gramG, firstProj_corner, firstProj_algebraMap, firstProj_conj_apply]
  have hG21 : ∀ a b, ph1 g (G (Sum.inr a) (Sum.inl b)) = (g.q : F)⁻¹ * (ph1 g (Zh b a) + cor r a b T) := by
    intro a b; rw [← hGd]; simp [gramG, firstProj_corner, firstProj_algebraMap]
  have hG22 : ∀ a b, ph1 g (G (Sum.inr a) (Sum.inr b)) =
      (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(ph1 g (Zh b a)) - ph2 g (Zh a b) - cor r a b (T + T')) := by
    intro a b; rw [← hGd]; simp [gramG, firstProj_corner, firstProj_algebraMap, firstProj_conj_apply]
  have hv1 : ∀ a, ph1 g (v (Sum.inl a)) = ph1 g (((w - w') a : M.R) : E) := by
    intro a; rw [← hv]; simp only [map_sub, firstProj_conj_iotaTwo, firstProj_iotaOne_inl, Pi.sub_apply]; push_cast
    rw [map_sub]
  have hv2 : ∀ a, ph1 g (v (Sum.inr a)) =
      (ph2 g (((w - w') a : M.R) : E) - ph1 g (((w - w') a : M.R) : E)) / (g.q : F) := by
    intro a; rw [← hv]; simp only [map_sub, firstProj_conj_iotaTwo, firstProj_iotaOne_inr, Pi.sub_apply]; push_cast
    simp only [map_sub]; ring
  have E1 : ∀ a, ∑ b, cor r a b (-T) * ph1 g (c (Sum.inl b)) +
      ∑ b, (g.q : F)⁻¹ * (ph2 g (Zh a b) + cor r a b T) * ph1 g (c (Sum.inr b)) =
        ph1 g (((w - w') a : M.R) : E) := by
    intro a; rw [← hv1, ← hrow, Fintype.sum_sum_type]; simp only [hG11, hG12]
  have E2 : ∀ a, ∑ b, (g.q : F)⁻¹ * (ph1 g (Zh b a) + cor r a b T) * ph1 g (c (Sum.inl b)) +
      ∑ b, (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(ph1 g (Zh b a)) - ph2 g (Zh a b) - cor r a b (T + T')) *
        ph1 g (c (Sum.inr b)) =
        (ph2 g (((w - w') a : M.R) : E) - ph1 g (((w - w') a : M.R) : E)) / (g.q : F) := by
    intro a; rw [← hv2, ← hrow, Fintype.sum_sum_type]; simp only [hG21, hG22]
  have hc1 : ∀ b, ph1 g (c (Sum.inl b)) ∈ 𝒪[F] := fun b => hint (Sum.inl b)
  have hc2 : ∀ b, ph1 g (c (Sum.inr b)) ∈ 𝒪[F] := fun b => hint (Sum.inr b)
  let m : Fin (r + 1) → M.R := fun b =>
    ⟨g.e.symm (ph1 g (c (Sum.inr b)), ph1 g (c (Sum.inr b)) - (g.q : F) * ph1 g (c (Sum.inl b))),
      mem_R_of hs _ ⟨_, hc2 b⟩ ⟨_, sub_mem (hc2 b) (mul_mem g.q.2 (hc1 b))⟩ ⟨_, hc1 b⟩ (by simp)
        (by show ph1 g (c (Sum.inr b)) - (ph1 g (c (Sum.inr b)) - (g.q : F) * ph1 g (c (Sum.inl b))) =
              (g.q : F) * ph1 g (c (Sum.inl b)); ring)⟩
  have hm1 : ∀ b, ph1 g ((m b : M.R) : E) = ph1 g (c (Sum.inr b)) := by intro b; simp [m, firstProj_apply]
  have hm2 : ∀ b, ph2 g ((m b : M.R) : E) = ph1 g (c (Sum.inr b)) - (g.q : F) * ph1 g (c (Sum.inl b)) := by
    intro b; simp [m, secondProj_apply]
  have htr : ((trO hs (m (Fin.last r)) : 𝒪[F]) : F) = ph1 g (c (Sum.inl (Fin.last r))) := by
    rw [trO_coe, ← firstProj_apply, ← secondProj_apply, hm1, hm2, div_eq_iff (q_ne g)]; ring
  have hZσ : ∀ a b, ((Zσ.Z a b : M.R) : E) = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b := by
    intro a b; have := congrFun (congrFun hG.2.2.2.2.1 a) b; simpa using this
  have hTT1 : ph1 g (TT : E) = T := by rw [firstProj_apply, hG.2.2.1]
  have hTT2 : ph2 g (TT : E) = T' := by rw [secondProj_apply, hG.2.2.1]
  have hcoe : ∀ a, ((llMap hs Zσ TT m a : M.R) : E) =
      ∑ b, ((Zσ.Z a b : M.R) : E) * ((m b : M.R) : E) -
        (TT : E) * algebraMap F E (ph1 g (c (Sum.inl (Fin.last r)))) * (((eV (M := M) r) a : M.R) : E) := by
    intro a
    simp only [llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct]
    push_cast
    rw [dgR_coe, htr]
  have heV1 : ∀ a, ph1 g (((eV (M := M) r) a : M.R) : E) = if a = Fin.last r then 1 else 0 := by
    intro a; by_cases ha : a = Fin.last r
    · subst ha; simp [eV]
    · simp [eV, ha]
  have heV2 : ∀ a, ph2 g (((eV (M := M) r) a : M.R) : E) = if a = Fin.last r then 1 else 0 := by
    intro a; by_cases ha : a = Fin.last r
    · subst ha; simp [eV]
    · simp [eV, ha]
  refine AddMonoidHom.mem_range.2 ⟨m, ?_⟩
  funext a
  apply Subtype.ext
  apply (eq_iff_ph (g := g) _ _).2
  constructor
  · rw [hcoe a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, hZσ, firstProj_zzPlus_conj hs, hm1, hTT1, firstProj_algebraMap, heV1]
    rw [← E1 a]
    have hk : T * ph1 g (c (Sum.inl (Fin.last r))) * (if a = Fin.last r then (1 : F) else 0) =
        ∑ b, cor r a b T * ph1 g (c (Sum.inl b)) := by
      rw [duU_sum_cor]; split_ifs <;> simp
    rw [hk]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold cor; split_ifs <;> ring
  · rw [hcoe a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, hZσ, secondProj_zzPlus_conj hs, hm2, hTT2, ph2_algebraMap_eq, heV2]
    have hD2 : ph2 g (((w - w') a : M.R) : E) = ph1 g (((w - w') a : M.R) : E) +
        (g.q : F) * ((ph2 g (((w - w') a : M.R) : E) - ph1 g (((w - w') a : M.R) : E)) / (g.q : F)) := by
      rw [mul_div_cancel₀ _ (q_ne g)]; ring
    rw [hD2, ← E2 a, ← E1 a]
    have hk : T' * ph1 g (c (Sum.inl (Fin.last r))) * (if a = Fin.last r then (1 : F) else 0) =
        ∑ b, cor r a b T' * ph1 g (c (Sum.inl b)) := by
      rw [duU_sum_cor]; split_ifs <;> simp
    rw [hk]
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hq := q_ne g
    unfold cor; split_ifs <;> field_simp <;> ring

def UnitGramG : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g → ∀ (r : ℕ) (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh Z Zσ →
    IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')).det

theorem stepDuU_of (hU : UnitGramG) : StepDuU := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ _ θ₁ θ₂ θ₂' hB hB'
  have hdet := hU F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H w =>
    obtain ⟨w₂, hw₂⟩ := QuotientAddGroup.mk_surjective (θ₂ (mk1 hs Zσ₁ TT w))
    obtain ⟨w₂', hw₂'⟩ := QuotientAddGroup.mk_surjective (θ₂' (mk1 hs Zσ₁ TT w))
    have key : w₂ - w₂' ∈ LL hs Zσ₂ TT := by
      refine duU_core hs h₂ hdet w₂ w₂' fun l₂ => ?_
      obtain ⟨l, hl⟩ := QuotientAddGroup.mk_surjective (θ₁.symm (mk1 hs Z₂ TT l₂))
      have hl' : θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ := by
        show θ₁ (QuotientAddGroup.mk l) = _
        rw [hl]; simp
      have e1 := hB l l₂ w w₂ hl' hw₂.symm
      have e2 := hB' l l₂ w w₂' hl' hw₂'.symm
      convert sub_mem e1 e2 using 1
      ring
    show θ₂ (QuotientAddGroup.mk w) = θ₂' (QuotientAddGroup.mk w)
    rw [← hw₂, ← hw₂']
    exact (QuotientAddGroup.eq_iff_sub_mem).2 key

end DuU2

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section DuU3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def duU_P (r : ℕ) (x : F) : Matrix (Ix r) (Ix r) F := Matrix.fromBlocks 1 (-x • 1) 0 (x • 1)

def duU_Gh (r : ℕ) (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (T T' : F) : Matrix (Ix r) (Ix r) F :=
  Matrix.fromBlocks (Matrix.of fun a b => cor r a b (-T)) A B.transpose (Matrix.of fun a b => cor r a b (-T'))

theorem secondProj_conj_apply (x : E) : ph2 g (M.L.cj x) = ph1 g x := secondProj_conj_eq_firstProj x

theorem duU_map_gramG (φ ψ : E →+* F) (hφ : ∀ x, φ (M.L.cj x) = ψ x) (hφa : ∀ a : F, φ (algebraMap F E a) = a)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F) :
    (gramG (M.L.cj : E →+* E) (algebraMap F E q⁻¹) Zh (algebraMap F E T) (algebraMap F E T')).map φ =
      (duU_P r q⁻¹).transpose * duU_Gh r (Zh.map ψ) (Zh.map φ) T T' * duU_P r q⁻¹ := by
  ext (a | a) (b | b) <;>
    simp [gramG, duU_Gh, duU_P, cor, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hφ, hφa,
      Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite φ] <;>
    split_ifs <;> ring

theorem duU_det_P (x : F) : (duU_P r x).det = x ^ (r + 1) := by
  simp [duU_P, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul]

theorem duU_inv_last (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F) :
    A⁻¹ (Fin.last r) (Fin.last r) = Ring.inverse A.det * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp

theorem duU_cor_mul_cor (N : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (s t : F) :
    (Matrix.of fun a b => cor r a b s) * N * (Matrix.of fun a b => cor r a b t) =
      Matrix.of fun a b => cor r a b (s * N (Fin.last r) (Fin.last r) * t) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, cor]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
    simp [ha, hb, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem duU_det_Gh (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (T T' : F) (hA : A.det ≠ 0)
    (h : A.det * B.det - T * T' * ((A.submatrix Fin.castSucc Fin.castSucc).det *
      (B.submatrix Fin.castSucc Fin.castSucc).det) ≠ 0) :
    (duU_Gh r A B T T').det ≠ 0 := by
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.2 hA)
  have hS : duU_Gh r A B T T' * Matrix.fromBlocks 0 1 1 0 =
      Matrix.fromBlocks A (Matrix.of fun a b => cor r a b (-T)) (Matrix.of fun a b => cor r a b (-T')) B.transpose := by
    simp [duU_Gh, Matrix.fromBlocks_multiply]
  have hdet : (duU_Gh r A B T T' * Matrix.fromBlocks 0 1 1 0).det =
      A.det * B.det - T * T' * ((A.submatrix Fin.castSucc Fin.castSucc).det *
        (B.submatrix Fin.castSucc Fin.castSucc).det) := by
    rw [hS, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, duU_cor_mul_cor]
    have hc : B.transpose - (Matrix.of fun a b => cor r a b (-T' * A⁻¹ (Fin.last r) (Fin.last r) * -T)) =
        B.transpose + Matrix.of fun a b => cor r a b (-(T' * A⁻¹ (Fin.last r) (Fin.last r) * T)) := by
      ext a b; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, cor]; split_ifs <;> ring
    rw [hc, det_add_cor, Matrix.det_transpose, duU_inv_last, Ring.inverse_eq_inv']
    have : (B.transpose.submatrix Fin.castSucc Fin.castSucc) = (B.submatrix Fin.castSucc Fin.castSucc).transpose := by
      ext a b; rfl
    rw [this, Matrix.det_transpose]
    field_simp
    ring
  intro h0
  apply h
  rw [← hdet, Matrix.det_mul, h0, zero_mul]

theorem unitGramG_holds : UnitGramG := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh Z Zσ hG
  have hZ := hG.2.2.2.2.2.1
  have hN := hG.2.2.2.2.2.2
  rw [isUnit_iff_ph (g := g)] at hZ hN ⊢
  have hq : (g.q : F)⁻¹ ≠ 0 := inv_ne_zero (q_ne g)
  constructor
  · rw [det_ph (ph1 g), duU_map_gramG (ph1 g) (ph2 g) (fun x => firstProj_conj_apply x) firstProj_algebraMap, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, duU_det_P]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) (duU_det_Gh _ _ _ _ ?_ ?_)) (pow_ne_zero _ hq)
    · rw [← det_ph]; exact hZ.2
    · convert hN.1 using 1
      simp only [map_sub, map_mul, firstProj_conj_apply, firstProj_algebraMap, det_ph (ph1 g), det_ph (ph2 g), Matrix.submatrix_map]
      ring
  · rw [det_ph (ph2 g), duU_map_gramG (ph2 g) (ph1 g) (fun x => secondProj_conj_apply x) ph2_algebraMap_eq, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, duU_det_P]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) (duU_det_Gh _ _ _ _ ?_ ?_)) (pow_ne_zero _ hq)
    · rw [← det_ph]; exact hZ.1
    · convert hN.2 using 1
      simp only [map_sub, map_mul, secondProj_conj_apply, ph2_algebraMap_eq, det_ph (ph1 g), det_ph (ph2 g), Matrix.submatrix_map]
      ring

theorem stepDuU : StepDuU := stepDuU_of unitGramG_holds

end DuU3

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
