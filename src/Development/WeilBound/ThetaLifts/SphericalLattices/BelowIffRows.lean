module

public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.LatDefs
noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k]

def IntM {m p : Type} (Z : Matrix m p k) : Prop := ∀ i j, Z i j ∈ 𝒪[k]

def Below {n d : ℕ} (t : k) (Y Y₀ : Matrix (Fin n) (Fin d) k) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) 𝒪[k], ∃ Z : Matrix (Fin n) (Fin d) k, IntM Z ∧
    Y = A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z

def latt {n d : ℕ} (t : k) (Y₀ : Matrix (Fin n) (Fin d) k) : Submodule 𝒪[k] (Fin d → k) :=
  Submodule.span 𝒪[k] (Set.range Y₀ ∪ Set.range fun j : Fin d => t • (Pi.single j 1 : Fin d → k))

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.LattEq
noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latt_eq {n d : ℕ} {t : k} (ht : t ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) k) :
    ∃ h : GL (Fin d) k, ∀ v : Fin d → k, v ∈ latt t Y₀ ↔ ∀ j, (v ᵥ* h.1) j ∈ 𝒪[k] := by
  classical
  set L := latt t Y₀ with hL
  have : Module.Finite 𝒪[k] L := by
    rw [hL, latt]
    exact Module.Finite.span_of_finite _ ((Set.finite_range _).union (Set.finite_range _))
  obtain ⟨m, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := 𝒪[k]) (M := L)
  set w : Fin m → (Fin d → k) := fun i => (b i : Fin d → k) with hw
  have hwL : ∀ i, w i ∈ L := fun i => (b i).2
  have hli : LinearIndependent k w := by
    rw [← LinearIndependent.iff_fractionRing 𝒪[k] k]
    exact b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hsum : ∀ x (hx : x ∈ L), x = ∑ i, ((b.repr ⟨x, hx⟩ i : 𝒪[k]) : k) • w i := by
    intro x hx
    have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    refine e.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact (algebraMap_smul k _ _).symm
  have hLw : ∀ x ∈ L, x ∈ Submodule.span k (Set.range w) := by
    intro x hx
    rw [hsum x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span k (Set.range w) := by
    intro x _
    have hx : x = ∑ j, (t⁻¹ * x j) • (t • Pi.single j (1 : k) : Fin d → k) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
    rw [hx]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hLw _ ?_)
    exact Submodule.subset_span (Or.inr ⟨j, rfl⟩)
  let bk := Module.Basis.mk hli hsp
  have hbk : ∀ i, bk i = w i := fun i => by simp [bk]
  have hm : m = d := by
    have := Module.finrank_eq_card_basis bk
    simpa using this.symm
  have hmem : ∀ v, v ∈ L ↔ ∀ i, bk.equivFun v i ∈ 𝒪[k] := by
    intro v
    constructor
    · intro hv i
      have : bk.equivFun v = fun i => ((b.repr ⟨v, hv⟩ i : 𝒪[k]) : k) := by
        apply bk.equivFun.symm.injective
        rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply]
        simpa only [hbk] using hsum v hv
      rw [this]
      exact (b.repr _ i).2
    · intro hc
      rw [← bk.sum_equivFun v]
      refine L.sum_mem fun i _ => ?_
      rw [hbk i, show bk.equivFun v i • w i = (⟨bk.equivFun v i, hc i⟩ : 𝒪[k]) • w i from rfl]
      exact L.smul_mem _ (hwL i)
  let bk' := bk.reindex (finCongr hm)
  let hmat : Matrix (Fin d) (Fin d) k := (LinearMap.toMatrix' bk'.equivFun.toLinearMap)ᵀ
  let Bmat : Matrix (Fin d) (Fin d) k := (LinearMap.toMatrix' bk'.equivFun.symm.toLinearMap)ᵀ
  have hB : hmat * Bmat = 1 := by
    simp only [hmat, Bmat, ← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨hmat, Bmat, hB, mul_eq_one_comm.mp hB⟩, fun v => ?_⟩
  have key : v ᵥ* hmat = bk'.equivFun v := by
    simp [hmat, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  have hre : ∀ j, bk'.equivFun v j = bk.equivFun v ((finCongr hm).symm j) := by
    intro j
    simp [bk', Module.Basis.equivFun_apply]
  show v ∈ L ↔ ∀ j, (v ᵥ* hmat) j ∈ 𝒪[k]
  rw [key, hmem]
  simp only [hre]
  exact ⟨fun H j => H _, fun H i => by simpa using H (finCongr hm i)⟩

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.ExistsIsUnitAddMul
noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel Matrix

theorem exists_isUnit_add_mul {K : Type} [Field K] {n : ℕ} (A D : Matrix (Fin n) (Fin n) K)
    (h : ∀ x, A *ᵥ x = 0 → D *ᵥ x = 0 → x = 0) : ∃ C : Matrix (Fin n) (Fin n) K, IsUnit (A + C * D).det := by
  classical
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl (LinearMap.range (Matrix.toLin' A))
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl ((LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D))
  have h1 : Module.finrank K ((LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D))
      = Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
    have hker : LinearMap.ker ((Matrix.toLin' D).domRestrict (LinearMap.ker (Matrix.toLin' A))) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro w hw
      have hw1 : A *ᵥ (w : Fin n → K) = 0 := by
        have := w.2
        rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      have hw2 : D *ᵥ (w : Fin n → K) = 0 := by
        simpa [Matrix.toLin'_apply] using hw
      exact Subtype.ext (h _ hw1 hw2)
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker)
  have h2 : Module.finrank K R = Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
    have e1 := Submodule.finrank_add_eq_of_isCompl hR
    have e2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
    omega
  let e := LinearEquiv.ofFinrankEq _ _ (h1.trans h2.symm)
  let proj := Submodule.linearProjOfIsCompl _ _ hU'
  let c : (Fin n → K) →ₗ[K] (Fin n → K) := R.subtype ∘ₗ e.toLinearMap ∘ₗ proj
  refine ⟨LinearMap.toMatrix' c, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ x, (A + LinearMap.toMatrix' c * D) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec] at hx
    have hcR : c (D *ᵥ x) ∈ R := (e (proj (D *ᵥ x))).2
    have haR : A *ᵥ x ∈ LinearMap.range (Matrix.toLin' A) := ⟨x, Matrix.toLin'_apply A x⟩
    have hax : A *ᵥ x = 0 := by
      have hneg : A *ᵥ x = -(c (D *ᵥ x)) := eq_neg_of_add_eq_zero_left hx
      have hmem : A *ᵥ x ∈ R := hneg ▸ R.neg_mem hcR
      exact (Submodule.disjoint_def.mp hR.disjoint) _ haR hmem
    have hcx : c (D *ᵥ x) = 0 := by
      rw [hax, zero_add] at hx
      exact hx
    have hDU : D *ᵥ x ∈ (LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D) :=
      ⟨x, by rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply]; exact hax,
        Matrix.toLin'_apply D x⟩
    have hproj : proj (D *ᵥ x) = ⟨D *ᵥ x, hDU⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hU' ⟨_, hDU⟩
    have hex : e ⟨D *ᵥ x, hDU⟩ = 0 := by
      have h3 : ((e (proj (D *ᵥ x)) : R) : Fin n → K) = 0 := hcx
      rw [hproj] at h3
      exact Subtype.ext h3
    have hDx : D *ᵥ x = 0 := by
      have h4 := congrArg Subtype.val (e.injective (hex.trans (map_zero e).symm))
      exact h4
    exact h x hax hDx
  intro x y hxy
  have hsub : (A + LinearMap.toMatrix' c * D) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbit {n d : ℕ} {t : k} {Y Y' : Matrix (Fin n) (Fin d) k} (h1 : Below t Y Y') (h2 : Below t Y' Y) :
    ∃ U : Matrix (Fin n) (Fin n) 𝒪[k], IsUnit U.det ∧ ∃ Z, IntM Z ∧ Y = U.map (algebraMap 𝒪[k] k) * Y' + t • Z := by
  classical
  obtain ⟨A, Z, hZ, hY⟩ := h1
  obtain ⟨B, Z', hZ', hY'⟩ := h2
  have hsurj := IsLocalRing.residue_surjective (R := 𝒪[k])
  obtain ⟨Cb, hCb⟩ := exists_isUnit_add_mul (A.map (IsLocalRing.residue 𝒪[k]))
    (1 - B.map (IsLocalRing.residue 𝒪[k]) * A.map (IsLocalRing.residue 𝒪[k])) (by
      intro x hx1 hx2
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx1, Matrix.mulVec_zero,
        sub_zero] at hx2
      exact hx2)
  let C : Matrix (Fin n) (Fin n) 𝒪[k] := Cb.map (Function.surjInv hsurj)
  have hC : C.map (IsLocalRing.residue 𝒪[k]) = Cb := by
    ext i j
    simp only [C, Matrix.map_apply]
    exact Function.surjInv_eq hsurj _
  let FinalForm : Matrix (Fin n) (Fin d) 𝒪[k] := Matrix.of fun i j => ⟨Z i j, hZ i j⟩
  let Zo' : Matrix (Fin n) (Fin d) 𝒪[k] := Matrix.of fun i j => ⟨Z' i j, hZ' i j⟩
  have hZo : FinalForm.map (algebraMap 𝒪[k] k) = Z := by
    ext i j
    rfl
  have hZo' : Zo'.map (algebraMap 𝒪[k] k) = Z' := by
    ext i j
    rfl
  refine ⟨A + C * (1 - B * A), ?_, (FinalForm - C * (B * FinalForm + Zo')).map (algebraMap 𝒪[k] k), ?_, ?_⟩
  · apply isUnit_of_map_unit (IsLocalRing.residue 𝒪[k])
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add (IsLocalRing.residue 𝒪[k]) (map_add _),
      Matrix.map_mul, Matrix.map_sub (IsLocalRing.residue 𝒪[k]) (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_mul, hC]
    exact hCb
  · intro i j
    exact ((FinalForm - C * (B * FinalForm + Zo')) i j).2
  · have hU : (A + C * (1 - B * A)).map (algebraMap 𝒪[k] k)
        = A.map (algebraMap 𝒪[k] k) + C.map (algebraMap 𝒪[k] k)
          * (1 - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k)) := by
      rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul]
    have hW : (FinalForm - C * (B * FinalForm + Zo')).map (algebraMap 𝒪[k] k)
        = Z - C.map (algebraMap 𝒪[k] k) * (B.map (algebraMap 𝒪[k] k) * Z + Z') := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hZo, hZo']
    have h2' : Y' = B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y'
        + t • (B.map (algebraMap 𝒪[k] k) * Z + Z') := by
      calc Y' = B.map (algebraMap 𝒪[k] k) * Y + t • Z' := hY'
        _ = B.map (algebraMap 𝒪[k] k) * (A.map (algebraMap 𝒪[k] k) * Y' + t • Z) + t • Z' := by rw [hY]
        _ = _ := by
          rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add]
          abel
    have e1 : Y' - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y'
        = t • (B.map (algebraMap 𝒪[k] k) * Z + Z') := by
      rw [sub_eq_iff_eq_add']
      exact h2'
    have e2 : (A.map (algebraMap 𝒪[k] k) + C.map (algebraMap 𝒪[k] k)
          * (1 - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k))) * Y'
        = A.map (algebraMap 𝒪[k] k) * Y' + C.map (algebraMap 𝒪[k] k)
          * (Y' - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y') := by
      rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
    rw [hU, hW, e2, e1, Matrix.mul_smul, smul_sub]
    conv_lhs => rw [hY]
    abel

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.ExistsVBallSubset
noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private def vBall {m p : Type} (r : k) : Set (Matrix m p k) :=
  {Z | ∀ i j, valuation k (Z i j) ≤ valuation k r}

private lemma isOpen_vle (r : k) (hr : r ≠ 0) : IsOpen {x : k | valuation k x ≤ valuation k r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 (valuation k r) (by simpa using hr), fun z hz => ?_⟩
  have h : z = (z - x) + x := by ring
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hz hx ⊢
  rw [h]
  exact (Valuation.map_add _ _ _).trans (max_le hz.le hx)

private lemma vBall_eq {m p : Type} (r : k) : (vBall r : Set (Matrix m p k)) =
    Set.pi Set.univ (fun _ : m => Set.pi Set.univ
      (fun _ : p => {x : k | valuation k x ≤ valuation k r})) := by
  ext Z
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩

private lemma isOpen_vBall {m p : Type} [Finite m] [Finite p] (r : k) (hr : r ≠ 0) :
    IsOpen (vBall r : Set (Matrix m p k)) := by
  rw [vBall_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_vle r hr

private lemma isCompact_vBall {m p : Type} (r : k) : IsCompact (vBall r : Set (Matrix m p k)) := by
  rw [vBall_eq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    IsNonarchimedeanLocalField.isCompact_closedBall k _

private lemma zero_mem_vBall {m p : Type} (r : k) : (0 : Matrix m p k) ∈ vBall r := by
  intro i j; simp

private lemma add_mem_vBall {m p : Type} {r : k} {Y Z : Matrix m p k} (hY : Y ∈ vBall r)
    (hZ : Z ∈ vBall r) : Y + Z ∈ vBall r := by
  intro i j
  simp only [Matrix.add_apply]
  exact (Valuation.map_add _ _ _).trans (max_le (hY i j) (hZ i j))

private lemma neg_mem_vBall {m p : Type} {r : k} {Y : Matrix m p k} (hY : Y ∈ vBall r) :
    -Y ∈ vBall r := by
  intro i j
  simpa [Matrix.neg_apply, Valuation.map_neg] using hY i j

private lemma vBall_mono {m p : Type} {r s : k} (h : valuation k r ≤ valuation k s) :
    (vBall r : Set (Matrix m p k)) ⊆ vBall s :=
  fun _ hZ i j => (hZ i j).trans h

private lemma smul_mem_vBall {m p : Type} (t : k) {Z : Matrix m p k} (hZ : IntM Z) :
    t • Z ∈ vBall t := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
  have := (Valuation.mem_integer_iff _ _).1 (hZ i j)
  calc _ ≤ valuation k t * 1 := mul_le_mul' le_rfl this
    _ = _ := mul_one _

private lemma exists_large {ι : Type} (s : Finset ι) (y : ι → k) :
    ∃ r : k, r ≠ 0 ∧ ∀ i ∈ s, valuation k (y i) ≤ valuation k r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨r, hr, h⟩ := ih
    rcases le_total (valuation k (y a)) (valuation k r) with hle | hle
    · refine ⟨r, hr, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hle
      · exact h i hi
    · rcases eq_or_ne (y a) 0 with h0 | h0
      · refine ⟨r, hr, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · simp [h0]
        · exact h i hi
      · refine ⟨y a, h0, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact le_rfl
        · exact (h i hi).trans hle

private lemma exists_small {ι : Type} (s : Finset ι) (f : ι → k) (hf : ∀ i ∈ s, f i ≠ 0) :
    ∃ t : k, t ≠ 0 ∧ t ∈ 𝒪[k] ∧ ∀ i ∈ s, valuation k t ≤ valuation k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, Subring.one_mem _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, ht, htO, h⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have htO' := (Valuation.mem_integer_iff _ _).1 htO
    rcases le_total (valuation k t) (valuation k (f a)) with hle | hle
    · refine ⟨t, ht, htO, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hle
      · exact h i hi
    · refine ⟨f a, hf a (Finset.mem_insert_self _ _), (Valuation.mem_integer_iff _ _).2
        (hle.trans htO'), fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_rfl
      · exact hle.trans (h i hi)

private lemma scalar_basis : (𝓝 (0 : k)).HasBasis (fun r : k => r ≠ 0)
    (fun r => {x : k | valuation k x ≤ valuation k r}) := by
  refine (IsValuativeTopology.hasBasis_nhds_zero' k).to_hasBasis ?_ ?_
  · intro γ hγ
    obtain ⟨a, rfl⟩ := ValuativeRel.valuation_surjective γ
    obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have ha : a ≠ 0 := by simpa using hγ
    have hw : w ≠ 0 := by simpa using hw0
    refine ⟨a * w, mul_ne_zero ha hw, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, map_mul] at hx ⊢
    exact hx.trans_lt (mul_lt_of_lt_one_right (zero_lt_iff.2 hγ) hw1)
  · intro r hr
    exact ⟨valuation k r, by simpa using hr,
      fun x hx => show valuation k x ≤ valuation k r from le_of_lt hx⟩

private lemma exists_vBall_subset {m p : Type} {U : Set (Matrix m p k)}
    (hU : U ∈ 𝓝 (0 : Matrix m p k)) : ∃ r : k, r ≠ 0 ∧ vBall r ⊆ U := by
  have hb2 := ((scalar_basis (k := k)).pi_self (ι := p)).pi_self (ι := m)
  have h0 : 𝓝 (0 : Matrix m p k) = Filter.pi (fun _ : m => Filter.pi (fun _ : p => 𝓝 (0 : k))) := by
    change 𝓝 (0 : m → p → k) = _
    rw [nhds_pi]
    congr 1
    funext i
    rw [nhds_pi]
    rfl
  rw [h0] at hU
  obtain ⟨⟨J, ⟨I, r⟩⟩, ⟨-, -, hr⟩, hsub⟩ := hb2.mem_iff.1 hU
  exact ⟨r, hr, fun Z hZ => hsub fun i _ j _ => hZ i j⟩

theorem sb_bound {m p : Type} [Fintype m] [Fintype p] {Φ : Matrix m p k → ℂ} (h1 : IsLocallyConstant Φ)
    (h2 : HasCompactSupport Φ) :
    ∃ t : k, t ≠ 0 ∧ t ∈ 𝒪[k] ∧ (∀ Y, Φ Y ≠ 0 → IntM (t • Y)) ∧ ∀ Y Z, IntM Z → Φ (Y + t • Z) = Φ Y := by
  classical
  have hKc : IsCompact (tsupport Φ) := h2
  haveI : Nonempty {s : k // s ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨s, hs0, hsK⟩ : ∃ s : k, s ≠ 0 ∧ tsupport Φ ⊆ vBall s := by
    obtain ⟨⟨s, hs⟩, h⟩ := hKc.elim_directed_cover (ι := {s : k // s ≠ 0})
      (fun s => (vBall s.1 : Set (Matrix m p k))) (fun s => isOpen_vBall s.1 s.2)
      (fun Y _ => by
        obtain ⟨r, hr, h⟩ := exists_large (Finset.univ : Finset (m × p)) (fun ij => Y ij.1 ij.2)
        exact Set.mem_iUnion.2 ⟨⟨r, hr⟩, fun i j => h (i, j) (Finset.mem_univ _)⟩)
      (fun a b => by
        rcases le_total (valuation k a.1) (valuation k b.1) with h | h
        · exact ⟨b, vBall_mono h, subset_rfl⟩
        · exact ⟨a, subset_rfl, vBall_mono h⟩)
    exact ⟨s, hs, h⟩
  have hloc : ∀ x : Matrix m p k, ∃ r : k, r ≠ 0 ∧ ∀ Z ∈ vBall r, Φ (x + Z) = Φ x := by
    intro x
    have hU : (fun Z => x + Z) ⁻¹' (Φ ⁻¹' {Φ x}) ∈ 𝓝 (0 : Matrix m p k) :=
      IsOpen.mem_nhds ((h1.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id))
        (by simp)
    obtain ⟨r, hr, hsub⟩ := exists_vBall_subset hU
    exact ⟨r, hr, fun Z hZ => hsub hZ⟩
  choose rr hrr0 hrr using hloc
  obtain ⟨S, -, hS⟩ := hKc.elim_nhds_subcover (fun x => (fun Y => Y - x) ⁻¹' vBall (rr x))
    (fun x _ => IsOpen.mem_nhds
      ((isOpen_vBall _ (hrr0 x)).preimage (continuous_id.sub continuous_const))
      (by simpa using zero_mem_vBall (m := m) (p := p) (rr x)))
  obtain ⟨t₁, ht₁0, -, ht₁⟩ := exists_small S rr (fun x _ => hrr0 x)
  have key : ∀ Y ∈ tsupport Φ, ∀ Z ∈ vBall t₁, Φ (Y + Z) = Φ Y := by
    intro Y hY Z hZ
    obtain ⟨x, hxS, hYx⟩ := Set.mem_iUnion₂.1 (hS hY)
    have hYx' : Y - x ∈ vBall (rr x) := hYx
    have hZ' : Z ∈ vBall (rr x) := vBall_mono (ht₁ x hxS) hZ
    have e1 : Φ Y = Φ x := by
      have := hrr x (Y - x) hYx'
      rwa [add_sub_cancel] at this
    have e2 : Φ (Y + Z) = Φ x := by
      have := hrr x (Y - x + Z) (add_mem_vBall hYx' hZ')
      rwa [show x + (Y - x + Z) = Y + Z by abel] at this
    rw [e1, e2]
  have hinv : ∀ Y, ∀ Z ∈ vBall t₁, Φ (Y + Z) = Φ Y := by
    intro Y Z hZ
    by_cases hY : Y ∈ tsupport Φ
    · exact key Y hY Z hZ
    by_cases hYZ : Y + Z ∈ tsupport Φ
    · have := key (Y + Z) hYZ (-Z) (neg_mem_vBall hZ)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYZ]
  obtain ⟨t, ht0, htO, ht⟩ := exists_small (Finset.univ : Finset (Fin 2)) ![t₁, s⁻¹]
    (fun i _ => by fin_cases i <;> simp [ht₁0, hs0])
  have ht1 : valuation k t ≤ valuation k t₁ := by simpa using ht 0 (Finset.mem_univ _)
  have hts : valuation k t ≤ valuation k s⁻¹ := by simpa using ht 1 (Finset.mem_univ _)
  refine ⟨t, ht0, htO, fun Y hY i j => ?_, fun Y Z hZ => hinv Y (t • Z) (vBall_mono ht1 (smul_mem_vBall t hZ))⟩
  have := hsK (subset_tsupport Φ hY) i j
  rw [Valuation.mem_integer_iff, Matrix.smul_apply, smul_eq_mul, map_mul]
  calc valuation k t * valuation k (Y i j) ≤ valuation k s⁻¹ * valuation k s := mul_le_mul' hts this
    _ = 1 := by rw [map_inv₀, inv_mul_cancel₀ (by simpa using hs0)]

theorem finite_cover {m p : Type} [Fintype m] [Fintype p] (t : k) (ht : t ≠ 0) :
    ∃ S : Finset (Matrix m p k), ∀ Y, IntM (t • Y) → ∃ y ∈ S, ∃ Z, IntM Z ∧ Y = y + t • Z := by
  classical
  have hc : IsCompact (vBall (m := m) (p := p) t⁻¹) := isCompact_vBall _
  obtain ⟨S, -, hS⟩ := hc.elim_nhds_subcover (fun x => (fun Y => Y - x) ⁻¹' vBall t)
    (fun x _ => IsOpen.mem_nhds
      ((isOpen_vBall _ ht).preimage (continuous_id.sub continuous_const))
      (by simpa using zero_mem_vBall (m := m) (p := p) t))
  refine ⟨S, fun Y hY => ?_⟩
  have hYb : Y ∈ vBall t⁻¹ := by
    intro i j
    have h := (Valuation.mem_integer_iff _ _).1 (hY i j)
    rw [Matrix.smul_apply, smul_eq_mul] at h
    rw [show Y i j = t⁻¹ * (t * Y i j) from (inv_mul_cancel_left₀ ht _).symm, map_mul]
    exact mul_le_of_le_one_right' h
  obtain ⟨y, hyS, hy⟩ := Set.mem_iUnion₂.1 (hS hYb)
  refine ⟨y, hyS, t⁻¹ • (Y - y), fun i j => ?_, ?_⟩
  · have h := hy i j
    rw [Valuation.mem_integer_iff, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    calc (valuation k t)⁻¹ * valuation k ((Y - y) i j) ≤ (valuation k t)⁻¹ * valuation k t :=
          mul_le_mul' le_rfl h
      _ = 1 := inv_mul_cancel₀ (by simpa using ht)
  · rw [smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel]

end PositivityTheory.Sph

end
end

noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel Matrix

section Int

variable {k : Type} [Field k] [ValuativeRel k]

theorem intM_zero {m p : Type} : IntM (0 : Matrix m p k) := fun _ _ => zero_mem _

theorem IntM.add {m p : Type} {Z Z' : Matrix m p k} (h : IntM Z) (h' : IntM Z') : IntM (Z + Z') :=
  fun i j => add_mem (h i j) (h' i j)

theorem IntM.sub {m p : Type} {Z Z' : Matrix m p k} (h : IntM Z) (h' : IntM Z') : IntM (Z - Z') :=
  fun i j => sub_mem (h i j) (h' i j)

theorem IntM.neg {m p : Type} {Z : Matrix m p k} (h : IntM Z) : IntM (-Z) := fun i j => neg_mem (h i j)

theorem IntM.smul {m p : Type} {c : k} (hc : c ∈ 𝒪[k]) {Z : Matrix m p k} (h : IntM Z) : IntM (c • Z) :=
  fun i j => mul_mem hc (h i j)

theorem intM_map {m p : Type} (A : Matrix m p 𝒪[k]) : IntM (A.map (algebraMap 𝒪[k] k)) := fun i j => (A i j).2

theorem IntM.mul {m p q : Type} [Fintype p] {P : Matrix m p k} {Q : Matrix p q k} (hP : IntM P) (hQ : IntM Q) :
    IntM (P * Q) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hP i l) (hQ l j)

variable {n d : ℕ}

theorem below_refl (t : k) (Y : Matrix (Fin n) (Fin d) k) : Below t Y Y :=
  ⟨1, 0, intM_zero, by simp [Matrix.map_one]⟩

theorem below_trans {t : k} {Y₁ Y₂ Y₃ : Matrix (Fin n) (Fin d) k} (h₁ : Below t Y₁ Y₂) (h₂ : Below t Y₂ Y₃) :
    Below t Y₁ Y₃ := by
  obtain ⟨A, Z, hZ, rfl⟩ := h₁
  obtain ⟨B, Z', hZ', rfl⟩ := h₂
  refine ⟨A * B, A.map (algebraMap 𝒪[k] k) * Z' + Z, (intM_map A).mul hZ' |>.add hZ, ?_⟩
  rw [Matrix.map_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add, add_assoc]

theorem below_int {t : k} (ht : t ∈ 𝒪[k]) {Y Y₀ : Matrix (Fin n) (Fin d) k} (h : Below t Y Y₀) (h₀ : IntM (t • Y₀)) :
    IntM (t • Y) := by
  obtain ⟨A, Z, hZ, rfl⟩ := h
  have : t • (A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z) = A.map (algebraMap 𝒪[k] k) * (t • Y₀) + t • (t • Z) := by
    rw [smul_add, Matrix.mul_smul]
  rw [this]
  exact ((intM_map A).mul h₀).add ((hZ.smul ht).smul ht)

theorem below_iff_rows (t : k) (Y Y₀ : Matrix (Fin n) (Fin d) k) : Below t Y Y₀ ↔ ∀ i, Y i ∈ latt t Y₀ := by
  constructor
  · rintro ⟨A, Z, hZ, rfl⟩ i
    have e : (A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z) i =
        ∑ l, A i l • Y₀ l + ∑ j, (⟨Z i j, hZ i j⟩ : 𝒪[k]) • (t • (Pi.single j 1 : Fin d → k)) := by
      funext j'
      simp [Matrix.mul_apply, Finset.sum_apply, Pi.single_apply, Subring.smul_def, mul_comm]
      exact Finset.sum_congr rfl fun _ _ => rfl
    rw [e]
    refine add_mem (sum_mem fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨l, rfl⟩)))
      (sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩)))
  · intro h
    have hr : Set.range Y₀ ∪ Set.range (fun j : Fin d => t • (Pi.single j 1 : Fin d → k)) =
        Set.range (Sum.elim Y₀ fun j : Fin d => t • (Pi.single j 1 : Fin d → k)) := (Set.Sum.elim_range _ _).symm
    have h' : ∀ i, ∃ c : Fin n ⊕ Fin d → 𝒪[k],
        ∑ x, c x • Sum.elim Y₀ (fun j : Fin d => t • (Pi.single j 1 : Fin d → k)) x = Y i := by
      intro i
      have := h i
      rw [latt, hr] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using h'
    refine ⟨Matrix.of fun i l => c i (Sum.inl l), Matrix.of fun i j => (c i (Sum.inr j) : k),
      fun i j => (c i (Sum.inr j)).2, ?_⟩
    ext i j
    have := congrFun (hc i) j
    rw [Fintype.sum_sum_type] at this
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← this]
    congr 1
    show ∑ x, (c i (Sum.inr x) : k) * (t • (Pi.single x 1 : Fin d → k)) j = _
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
    simp [mul_comm]

end Int

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

theorem below_iff {t : k} (ht : t ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) k) :
    ∃ h : GL (Fin d) k, ∀ Y, Below t Y Y₀ ↔ IntM (Y * h.1) := by
  obtain ⟨h, hh⟩ := latt_eq ht Y₀
  refine ⟨h, fun Y => ?_⟩
  rw [below_iff_rows]
  simp only [hh, IntM]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

def bsetoid (t : k) : Setoid (Matrix (Fin n) (Fin d) k) where
  r Y Y' := Below t Y Y' ∧ Below t Y' Y
  iseqv := ⟨fun Y => ⟨below_refl t Y, below_refl t Y⟩, fun h => ⟨h.2, h.1⟩,
    fun h h' => ⟨below_trans h.1 h'.1, below_trans h'.2 h.2⟩⟩

theorem mk_eq_iff {t : k} {Y Y' : Matrix (Fin n) (Fin d) k} :
    Quotient.mk (bsetoid t) Y = Quotient.mk (bsetoid t) Y' ↔ Below t Y Y' ∧ Below t Y' Y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem out_rel {t : k} (Y : Matrix (Fin n) (Fin d) k) :
    Below t (Quotient.mk (bsetoid t) Y).out Y ∧ Below t Y (Quotient.mk (bsetoid t) Y).out :=
  mk_eq_iff.1 (Quotient.out_eq _)

def gens (k : Type) [Field k] [ValuativeRel k] (n d : ℕ) : Set (Matrix (Fin n) (Fin d) k → ℂ) :=
  {f | ∃ h : GL (Fin d) k, f = fun Y => Set.indicator {Z : Matrix (Fin n) (Fin d) k | ∀ i j, Z i j ∈ 𝒪[k]}
    (fun _ => (1 : ℂ)) (Y * h.1)}

theorem latSt : LatSt := by
  intro k _ _ _ _ n d Φ hΦ hK
  classical
  obtain ⟨h1, h2⟩ := hΦ
  obtain ⟨t, ht0, htO, hsupp, hinv⟩ := sb_bound h1 h2
  obtain ⟨S, hS⟩ := finite_cover (m := Fin n) (p := Fin d) t ht0

  have key : ∀ Y Y', Below t Y Y' → Below t Y' Y → Φ Y = Φ Y' := by
    intro Y Y' a b
    obtain ⟨U, hU, Z, hZ, rfl⟩ := orbit a b
    rw [hinv _ _ hZ]
    have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).2 hU
    have := hK (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit) ⟨hu.unit, rfl⟩ Y'
    have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        U.map (algebraMap 𝒪[k] k) := rfl
    rw [← e]
    exact this
  set s := bsetoid (n := n) (d := d) t with hs
  set T : Finset (Quotient s) := (S.filter fun y => IntM (t • y)).image (Quotient.mk s) with hT
  have memT : ∀ Y, IntM (t • Y) → Quotient.mk s Y ∈ T := by
    intro Y hY
    obtain ⟨y, hy, Z, hZ, rfl⟩ := hS Y hY
    have hy' : IntM (t • y) := by
      have e : t • y = t • (y + t • Z) - t • (t • Z) := by rw [smul_add]; abel
      rw [e]; exact hY.sub ((hZ.smul htO).smul htO)
    refine Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hy, hy'⟩, mk_eq_iff.2 ⟨?_, ?_⟩⟩
    · exact ⟨1, -Z, hZ.neg, by simp [Matrix.map_one]⟩
    · exact ⟨1, Z, hZ, by simp [Matrix.map_one]⟩
  have outT : ∀ c ∈ T, IntM (t • c.out) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    exact below_int htO (out_rel y).1 (Finset.mem_filter.1 hy).2
  let e : Quotient s → Matrix (Fin n) (Fin d) k → ℂ := fun c Y => if Quotient.mk s Y = c then 1 else 0
  let F : Quotient s → Finset (Quotient s) := fun c => T.filter fun c' => Below t c'.out c.out ∧ c' ≠ c
  have hi : ∀ c ∈ T, (fun Y => if Below t Y c.out then (1 : ℂ) else 0) ∈ Submodule.span ℂ (gens k n d) := by
    intro c _
    obtain ⟨h, hh⟩ := below_iff ht0 c.out
    refine Submodule.subset_span ⟨h, funext fun Y => ?_⟩
    by_cases hY : Below t Y c.out
    · rw [if_pos hY, Set.indicator_of_mem ((hh Y).1 hY)]
    · rw [if_neg hY, Set.indicator_of_notMem (fun h' => hY ((hh Y).2 h'))]
  have hdec : ∀ c ∈ T, (fun Y => if Below t Y c.out then (1 : ℂ) else 0) = e c + ∑ c' ∈ F c, e c' := by
    intro c hc
    funext Y
    simp only [Pi.add_apply, Finset.sum_apply]
    by_cases hB : Below t Y c.out
    · rw [if_pos hB]
      have hq : Quotient.mk s Y ∈ T := memT Y (below_int htO hB (outT c hc))
      by_cases hqc : Quotient.mk s Y = c
      · have h0 : ∑ c' ∈ F c, e c' Y = 0 := Finset.sum_eq_zero fun c' hc' => by
          simp only [e]
          rw [if_neg]
          intro h
          exact (Finset.mem_filter.1 hc').2.2 (h.symm.trans hqc)
        rw [h0, add_zero]
        simp only [e]
        rw [if_pos hqc]
      · have h0 : ∑ c' ∈ F c, e c' Y = 1 := by
          simp only [e]
          rw [Finset.sum_ite_eq, if_pos]
          exact Finset.mem_filter.2 ⟨hq, below_trans (out_rel Y).1 hB, hqc⟩
        rw [h0]
        simp only [e]
        rw [if_neg hqc, zero_add]
    · rw [if_neg hB]
      have h1 : e c Y = 0 := by
        simp only [e]
        rw [if_neg]
        intro h
        apply hB
        rw [← h]
        exact (out_rel Y).2
      have h2 : ∑ c' ∈ F c, e c' Y = 0 := Finset.sum_eq_zero fun c' hc' => by
        simp only [e]
        rw [if_neg]
        intro h
        apply hB
        have h3 := (Finset.mem_filter.1 hc').2.1
        rw [← h] at h3
        exact below_trans (out_rel Y).2 h3
      rw [h1, h2, add_zero]
  have he : ∀ m, ∀ c ∈ T, (F c).card = m → e c ∈ Submodule.span ℂ (gens k n d) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro c hc hm
      have hsum : ∑ c' ∈ F c, e c' ∈ Submodule.span ℂ (gens k n d) := by
        refine Submodule.sum_mem _ fun c' hc' => ?_
        have hc'T := (Finset.mem_filter.1 hc').1
        refine ih (F c').card ?_ c' hc'T rfl
        rw [← hm]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨c', hc', fun h => (Finset.mem_filter.1 h).2.2 rfl⟩
        · intro c'' hc''
          obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hc''
          obtain ⟨-, h4, h5⟩ := Finset.mem_filter.1 hc'
          refine Finset.mem_filter.2 ⟨h1, below_trans h2 h4, fun h => h5 ?_⟩
          rw [← Quotient.out_eq c', ← Quotient.out_eq c]
          refine mk_eq_iff.2 ⟨h4, ?_⟩
          rw [← h]
          exact h2
      have := Submodule.sub_mem _ (hi c hc) hsum
      rw [hdec c hc, add_sub_cancel_right] at this
      exact this
  have hΦ : Φ = ∑ c ∈ T, Φ c.out • e c := by
    funext Y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, e, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hY : IntM (t • Y)
    · rw [if_pos (memT Y hY)]
      exact key _ _ (out_rel Y).2 (out_rel Y).1
    · rw [if_neg]
      · by_contra h
        exact hY (hsupp Y h)
      · intro hq
        exact hY (below_int htO (out_rel Y).2 (outT _ hq))
  rw [hΦ]
  exact Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (he _ c hc rfl)

end PositivityTheory.Sph

end
