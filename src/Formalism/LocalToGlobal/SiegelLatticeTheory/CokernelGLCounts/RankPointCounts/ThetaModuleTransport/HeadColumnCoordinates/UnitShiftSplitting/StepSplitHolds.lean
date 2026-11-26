module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.GammaOneNonempty
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjApply

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FormSplit
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

section FormSplit

theorem fs_add_left (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y Y' W : Ix r → O) :
    formG O cj qi Z T T' (Y + Y') W = formG O cj qi Z T T' Y W + formG O cj qi Z T T' Y' W := by
  unfold formG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Subring.coe_add]
  ring

theorem fs_add_right (O : Subring E) (cj : E →+* E) (qi : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : E) (Y W W' : Ix r → O) :
    formG O cj qi Z T T' Y (W + W') = formG O cj qi Z T T' Y W + formG O cj qi Z T T' Y W' := by
  unfold formG
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Subring.coe_add, map_add (f := _)]
  ring

theorem splitSecondProj_iotaOne (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph2 g ((iota1 hs l i : M.L.O) : E) = 0 := by
  rcases i with a | a
  · rw [secondProj_apply, e_iota1_inl]
  · rw [secondProj_apply, e_iota1_inr]

theorem splitFirstProj_iotaTwo (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g ((iota2 hs l i : M.L.O) : E) = 0 := by
  rw [firstProj_apply, e_iota2]

theorem splitSecondProj_conj (x : E) : ph2 g ((M.L.cj : E →+* E) x) = ph1 g x := secondProj_conj_eq_firstProj x

theorem splitForm_iotaOne_iotaOne (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
      (iota1 hs l) (iota1 hs w) = 0 := by
  rw [eq_iff_ph (g := g)]
  unfold formG
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, splitSecondProj_conj, splitSecondProj_iotaOne, mul_zero, zero_mul,
    Finset.sum_const_zero]
  simp

theorem splitForm_iotaTwo_iotaTwo (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
      (iota2 hs l) (iota2 hs w) = 0 := by
  rw [eq_iff_ph (g := g)]
  unfold formG
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_zero, firstProj_conj_eq_secondProj, splitSecondProj_conj, splitFirstProj_iotaTwo, mul_zero, zero_mul,
    Finset.sum_const_zero]
  simp

theorem fs_map_inv {n : Type} [Fintype n] [DecidableEq n] (f : E →+* E) (A : Matrix n n E) (hA : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

theorem fs_gram_herm (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F) (i j : Ix r) :
    (M.L.cj : E →+* E) (gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') j i) =
      gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') i j := by
  rcases i with a | a <;> rcases j with b | b <;> by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
    simp [gramG, cor, ha, hb, map_mul, map_add (f := _), map_neg, map_sub, M.L.cj_cj, AlgEquiv.commutes] <;> ring

theorem fs_herm (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F)
    (hU : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T')).det)
    (Y W : Ix r → M.L.O) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') Y W =
      (M.L.cj : E →+* E)
        (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') W Y) := by
  obtain ⟨G, hGd⟩ : ∃ G, gramG (M.L.cj : E →+* E) (algebraMap F E q) Zh (algebraMap F E T) (algebraMap F E T') = G :=
    ⟨_, rfl⟩
  rw [hGd] at hU
  have hT : G.map (M.L.cj : E →+* E) = G.transpose := by
    ext i j; rw [Matrix.map_apply, Matrix.transpose_apply, ← hGd, fs_gram_herm]
  have hinv : ∀ i j, (M.L.cj : E →+* E) (G⁻¹ i j) = G⁻¹ j i := by
    intro i j
    have := congrFun (congrFun (fs_map_inv (M.L.cj : E →+* E) G hU) i) j
    rw [Matrix.map_apply] at this
    have h2 : (G.transpose)⁻¹ = (G⁻¹).transpose := by rw [Matrix.transpose_nonsing_inv]
    rw [this, hT, h2, Matrix.transpose_apply]
  have hcc : ∀ x : E, (M.L.cj : E →+* E) ((M.L.cj : E →+* E) x) = x := M.L.cj_cj
  unfold formG
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hGd, map_sum, map_mul, hcc, hinv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem fs_split (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hU : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det)
    (Y W : Ix r → M.L.O) :
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T') Y W =
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
          (iota1 hs (cmp1 hs Y)) (iota2 hs (cmp2 hs W)) +
        (M.L.cj : E →+* E) (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
          (algebraMap F E T') (iota1 hs (cmp1 hs W)) (iota2 hs (cmp2 hs Y))) := by
  conv_lhs => rw [← iota_cmp hs Y, ← iota_cmp hs W]
  rw [fs_add_left, fs_add_right, fs_add_right, splitForm_iotaOne_iotaOne, splitForm_iotaTwo_iotaTwo,
    fs_herm Zh T T' _ hU (iota2 hs (cmp2 hs Y)) (iota1 hs (cmp1 hs W))]
  ring

theorem fs_rel (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)} (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT) (Y Y₂ : Ix r → M.L.O) :
    thetaOf hs h₁ h₂ θ₁ θ₂ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₂ ↔
      θ₁ (QuotientAddGroup.mk (cmp1 hs Y)) = QuotientAddGroup.mk (cmp1 hs Y₂) ∧
        θ₂ (QuotientAddGroup.mk (cmp2 hs Y)) = QuotientAddGroup.mk (cmp2 hs Y₂) := by
  rw [thetaOf, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  simp [splitH, splitQ_mk, Prod.ext_iff]
  exact Iff.rfl

theorem formSplit_holds : FormSplitP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ θ₁ θ₂
  have hU₁ := unitGramG_holds F E M g hs r T T' TT Zh₁ Z₁ Zσ₁ h₁
  have hU₂ := unitGramG_holds F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂
  constructor
  · intro hF l l₂ w w₂ hl hw
    refine hF (iota1 hs l) (iota2 hs w) (iota1 hs l₂) (iota2 hs w₂) ?_ ?_
    · rw [fs_rel, firstComponent_iotaOne, firstComponent_iotaOne, secondComponent_iotaOne, secondComponent_iotaOne]
      exact ⟨hl, by simp⟩
    · rw [fs_rel, firstComponent_iotaTwo, firstComponent_iotaTwo, secondComponent_iotaTwo, secondComponent_iotaTwo]
      exact ⟨by simp, hw⟩
  · intro hB Y W Y₂ W₂ hY hW
    rw [fs_rel] at hY hW
    rw [fs_split hs Zh₂ T T' hU₂, fs_split hs Zh₁ T T' hU₁]
    have e1 := hB (cmp1 hs Y) (cmp1 hs Y₂) (cmp2 hs W) (cmp2 hs W₂) hY.1 hW.2
    have e2 := hB (cmp1 hs W) (cmp1 hs W₂) (cmp2 hs Y) (cmp2 hs Y₂) hW.1 hY.2
    have e2' : (M.L.cj : E →+* E) (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂
        (algebraMap F E T) (algebraMap F E T') (iota1 hs (cmp1 hs W₂)) (iota2 hs (cmp2 hs Y₂)) -
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T) (algebraMap F E T')
        (iota1 hs (cmp1 hs W)) (iota2 hs (cmp2 hs Y))) ∈ M.L.O := cj_mem_O M.L e2
    convert add_mem e1 e2' using 1
    rw [map_sub]
    ring

end FormSplit

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondProjUniformizerMul
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

theorem firstProj_firstComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) : p1 g (cmp1 hs Y b : E) = p1 g (Y (Sum.inl b)) := by
  simp [p1, cmp1, e_rOf, c1]
theorem secondProj_firstComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) :
    p2 g (cmp1 hs Y b : E) = p1 g (Y (Sum.inl b)) + (g.q : F) * p1 g (Y (Sum.inr b)) := by
  simp [p1, p2, cmp1, e_rOf, c1]
theorem firstProj_secondComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) : p1 g (cmp2 hs Y b : E) = p2 g (Y (Sum.inl b)) := by
  simp [p1, p2, cmp2, e_rOf, c2]
theorem secondProj_secondComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) :
    p2 g (cmp2 hs Y b : E) = p2 g (Y (Sum.inl b)) + (g.q : F) * p2 g (Y (Sum.inr b)) := by
  simp [p1, p2, cmp2, e_rOf, c2]
theorem firstProj_uniformizer_mul (x : M.R) : p1 g ((q2 hs * x : M.R) : E) = 0 := by
  simp [p1, q2]
theorem secondProj_uniformizer_mul (x : M.R) : p2 g ((q2 hs * x : M.R) : E) = (g.q : F) * p2 g (x : E) := by
  simp [p2, q2]

theorem dl_cast (a : Fin r) : dl (F := F) r a.castSucc = 0 := by
  unfold dl
  rw [if_neg (Fin.castSucc_lt_last a).ne]

theorem gamSup_holds : GamSupP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh Z Zσ h
  rintro _ ⟨⟨a, b⟩, ⟨⟨l, η, rfl⟩, ⟨l', η', rfl⟩⟩, rfl⟩
  have hZh : IsUnit Zh.det := h.2.2.2.2.2.1
  set u : Fin (r + 1) → M.R := η • (eV r : Fin (r + 1) → M.R) + q2 hs • l
  set u' : Fin (r + 1) → M.R := η' • (eV r : Fin (r + 1) → M.R) + q2 hs • l'
  set Y : Ix r → M.L.O := iota1 hs u + iota2 hs u'
  set Y'' : Ix r → M.L.O := iota1 hs l + iota2 hs l'
  set Y' : Ix r → M.L.O := Y - dgO g g.q • Y''
  have h1 : cmp1 hs Y = u := by simp only [Y, map_add (f := _), firstComponent_iotaOne, firstComponent_iotaTwo, add_zero]
  have h2 : cmp2 hs Y = u' := by simp only [Y, map_add (f := _), secondComponent_iotaOne, secondComponent_iotaTwo, zero_add]
  have h3 : cmp1 hs Y'' = l := by simp only [Y'', map_add (f := _), firstComponent_iotaOne, firstComponent_iotaTwo, add_zero]
  have h4 : cmp2 hs Y'' = l' := by simp only [Y'', map_add (f := _), secondComponent_iotaOne, secondComponent_iotaTwo, zero_add]
  have hY : ∀ i, (Y i : E) - Y' i = algebraMap F E (g.q : F) * Y'' i := fun i => by
    simp only [Y', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dgO, AddSubgroupClass.coe_sub,
      MulMemClass.coe_mul]
    ring
  have hW1 : ∀ i, p1 g (Y' i) = p1 g (Y i) - (g.q : F) * p1 g (Y'' i) := fun i => by
    have := congrArg (p1 g) (hY i); rw [map_sub, map_mul, firstProj_algebraMap_split] at this; linear_combination -this
  have hW2 : ∀ i, p2 g (Y' i) = p2 g (Y i) - (g.q : F) * p2 g (Y'' i) := fun i => by
    have := congrArg (p2 g) (hY i); rw [map_sub, map_mul, secondProj_algebraMap_split] at this; linear_combination -this
  have fY := components_of_firstComponent_eq hs h1
  have gY := components_of_secondComponent_eq hs h2
  have fZ := components_of_firstComponent_eq hs h3
  have gZ := components_of_secondComponent_eq hs h4
  simp only [u, u', firstProj_unit_vector_eq hs, secondProj_unit_vector_eq hs] at fY gY
  refine ⟨Y, Y', Y'', fun a => ?_, fun a => ?_, hY, ?_⟩
  · apply Subtype.ext
    apply E_ext (g := g)
    · rw [(fY _).1, dl_cast, mul_zero, ZeroMemClass.coe_zero, map_zero]
    · rw [(gY _).1, dl_cast, mul_zero, ZeroMemClass.coe_zero, map_zero]
  · apply E_ext (g := g)
    · rw [map_add (f := _), map_mul, firstProj_algebraMap_split, hW1, hW1, map_zero]
      linear_combination (fY a.castSucc).2 - (g.q : F) * (fZ a.castSucc).2 + p2 g η * dl_cast (F := F) a
    · rw [map_add (f := _), map_mul, secondProj_algebraMap_split, hW2, hW2, map_zero]
      linear_combination (gY a.castSucc).2 - (g.q : F) * (gZ a.castSucc).2 + p2 g η' * dl_cast (F := F) a
  · exact Prod.ext rfl (Prod.ext rfl (vals hs hZh T T' h1 h2 h3 h4 hY).symm)

theorem gamSub_holds : GamSubP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh Z Zσ h
  rintro _ ⟨Y, Y', Y'', c1, c2, c3, rfl⟩
  have hZh : IsUnit Zh.det := h.2.2.2.2.2.1
  set l := cmp1 hs Y''
  set l' := cmp2 hs Y''
  set η : M.R := cmp1 hs Y (Fin.last r) - q2 hs * l (Fin.last r)
  set η' : M.R := cmp2 hs Y (Fin.last r) - q2 hs * l' (Fin.last r)
  have hW1 : ∀ i, p1 g (Y' i) = p1 g (Y i) - (g.q : F) * p1 g (Y'' i) := fun i => by
    have := congrArg (p1 g) (c3 i); rw [map_sub, map_mul, firstProj_algebraMap_split] at this; linear_combination -this
  have hW2 : ∀ i, p2 g (Y' i) = p2 g (Y i) - (g.q : F) * p2 g (Y'' i) := fun i => by
    have := congrArg (p2 g) (c3 i); rw [map_sub, map_mul, secondProj_algebraMap_split] at this; linear_combination -this
  have h1 : cmp1 hs Y = η • (eV r : Fin (r + 1) → M.R) + q2 hs • l := by
    funext b
    apply R_ext (g := g)
    · rw [firstProj_unit_vector_eq hs, firstProj_firstComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η, AddSubgroupClass.coe_sub, map_sub, firstProj_uniformizer_mul, firstProj_firstComponent, dl_last, mul_one, sub_zero]
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        rw [c1 a, dl_cast, mul_zero, ZeroMemClass.coe_zero, map_zero]
    · rw [secondProj_unit_vector_eq hs, secondProj_firstComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η, l, AddSubgroupClass.coe_sub, map_sub, secondProj_uniformizer_mul, secondProj_firstComponent, dl_last, mul_one]
        ring
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        have e := congrArg (p1 g) (c2 a)
        rw [map_add (f := _), map_mul, firstProj_algebraMap_split, hW1, hW1, map_zero] at e
        simp only [l, secondProj_firstComponent, dl_cast, mul_zero, zero_add]
        linear_combination e
  have h2 : cmp2 hs Y = η' • (eV r : Fin (r + 1) → M.R) + q2 hs • l' := by
    funext b
    apply R_ext (g := g)
    · rw [firstProj_unit_vector_eq hs, firstProj_secondComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η', AddSubgroupClass.coe_sub, map_sub, firstProj_uniformizer_mul, firstProj_secondComponent, dl_last, mul_one, sub_zero]
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        have e := congrArg Prod.snd (congrArg g.e (congrArg Subtype.val (c1 a)))
        rw [dl_cast, mul_zero]
        simpa [adele_ext_components] using e
    · rw [secondProj_unit_vector_eq hs, secondProj_secondComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η', l', AddSubgroupClass.coe_sub, map_sub, secondProj_uniformizer_mul, secondProj_secondComponent, dl_last, mul_one]
        ring
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        have e := congrArg (p2 g) (c2 a)
        rw [map_add (f := _), map_mul, secondProj_algebraMap_split, hW2, hW2, map_zero] at e
        simp only [l', secondProj_secondComponent, dl_cast, mul_zero, zero_add]
        linear_combination e
  refine ⟨(((QuotientAddGroup.mk (cmp1 hs Y) : DD1 hs Z TT), (QuotientAddGroup.mk l : DD1 hs Z TT), η,
      laG (ZZm g Zh T T') l), ((QuotientAddGroup.mk (cmp2 hs Y) : DD1 hs Zσ TT),
      (QuotientAddGroup.mk l' : DD1 hs Zσ TT), η', laG (ZZm g (Zh.map M.L.cj) T T') l')),
    ⟨⟨l, η, by rw [h1]⟩, ⟨l', η', by rw [h2]⟩⟩, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact (splitH hs h).symm_apply_apply (Submodule.Quotient.mk Y)
  · exact (splitH hs h).symm_apply_apply (Submodule.Quotient.mk Y'')
  · exact (vals hs hZh T T' h1 h2 rfl rfl c3).symm

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

theorem gamSplit_holds : GamSplitP := gamSplit_of gamSub_holds gamSup_holds

theorem stepSplit_holds : Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.StepSplit := stepSplit_of gamSplit_holds formSplit_holds

end Formalism.L2.SG.LocalCountModules.AlgGSplit
