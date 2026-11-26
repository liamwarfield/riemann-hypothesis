module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralMatrixSplitPlaceMemStdHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralMatrixSplitPlaceMemStdHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitUpStd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul' (q : GlobalTheory.FinPl.SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]

set_option maxHeartbeats 800000 in
theorem int_up_mem_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (a₀ : D.host.E), a₀ ∈ (D.host.AA : Set D.host.E) → q.pr (incA D a₀) ≠ 0 → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = q.pr (incA D a₀) • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T := by
  intro D k _ _ _ _ q S T a₀ ha₀ _ FS FT hβ _ hγ t ht
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]

  let G : Fin T.rank → Fin S.rank → WO S T := fun i l =>
    Matrix.of fun i' j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)
  have hsingle : ∀ (n : ℕ) (l : Fin n), (Pi.single l (1 : D.host.E) : Fin n → D.host.E) ∈ intVecSub D n := by
    intro n l m
    by_cases hm : m = l
    · subst hm; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hm]; exact isIntegral_zero
  have hG : ∀ i l, G i l ∈ stdHom S T := fun i l =>
    Formalism.IndefR.Fin.gen_mem S T (intVecSub D S.rank) (intVecSub D T.rank) hα ha₀ (hsingle _ l) (hsingle _ i)
  have htm : ∀ (x : k) (y : D.host.E), q.sec x * (pairA D.host.F 0 α ⊗ₜ[D.host.F] y) = q.sec (x * q.pr (incA D y)) := by
    intro x y
    have e1 : pairA D.host.F 0 α ⊗ₜ[D.host.F] y = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D y := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have h2 : q.e * q.sec x = q.sec x := by rw [← q.sec_pr, q.pr_sec]
    rw [e1, ← mul_assoc, ← h2, mul_assoc q.e, mul_comm (q.sec x), ← mul_assoc q.e, hee, h2, sec_mul']
  have hrow : ∀ (l : Fin S.rank) j,
      ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j = S.gram l j := by
    intro l j
    rw [Finset.sum_eq_single l]
    · rw [Pi.single_eq_same, star_one, one_mul]
    · intro m _ hm; rw [Pi.single_eq_of_ne hm, star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ l) h
  have hGapp : ∀ i l i' j, (q.sec (t i l) • G i l) i' j = q.sec (t i l) * (pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)) := fun _ _ _ _ => rfl
  have key : (Place.ofSplitPt q).up FS FT t = ∑ i, ∑ l, q.sec (t i l) • G i l := by
    ext i' j
    change q.sec ((FT.β * t * FS.γ) i' j) = _
    rw [hβ, hγ, Matrix.one_mul, Matrix.sum_apply, Finset.sum_eq_single i']
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [Matrix.sum_apply, Matrix.mul_apply, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hGapp, htm, hrow, Pi.single_eq_same, mul_one, map_mul (incA D), map_mul q.pr, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    · intro i _ hi
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hGapp, Pi.single_eq_of_ne (Ne.symm hi), mul_zero, zero_mul, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i') h
  rw [key]
  refine sum_mem fun i _ => sum_mem fun l _ => ?_
  exact Formalism.IndefR.Fin.latO_smul_mem S T (intVecSub D S.rank) (intVecSub D T.rank) ((q.int_iff _).1 (ht i l)) (hG i l)

end GlobalTheory.SplitUpStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralMatrixSplitPlaceMemStdHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_matrix_split_place_mem_stdHomLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (a₀ : D.host.E), a₀ ∈ (D.host.AA : Set D.host.E) → q.pr (incA D a₀) ≠ 0 → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = q.pr (incA D a₀) • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T := by
  first | exact @GlobalTheory.SplitUpStd.int_up_mem_stdHom | exact GlobalTheory.SplitUpStd.int_up_mem_stdHom | (intros; apply GlobalTheory.SplitUpStd.int_up_mem_stdHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdHomLatticePointIntegralMatrixAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdHomLatticePointIntegralMatrixAtSplitPlace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.StdHomDown

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_int_of_isIntegral (q : GlobalTheory.FinPl.SplitPt D k) {x : D.host.E} (hx : IsIntegral ℤ x) :
    q.pr (incA D x) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D x)) := hx.map ((q.pr.comp (incA D)).toIntAlgHom)
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h1.tower_top

theorem star_isIntegral {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem tmul_eq (α : AF D.host.F) (y : D.host.E) :
    (α ⊗ₜ[D.host.F] y : AE D) = algebraMap (AF D.host.F) (AE D) α * incA D y := by
  change _ = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem down_mem_integer : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (c : k), c ≠ 0 → (∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / c ∈ 𝒪[k]) → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = c • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k] := by
  intro D k _ _ _ _ q S T c hc hAA FS FT _ hγT hγS u hu
  set Gw : Matrix (Fin S.rank) (Fin S.rank) k := (HSpace.gram S).map (fun a => q.pr (incA D a)) with hGw
  have hGβ : Gw * FS.β = c⁻¹ • (1 : Matrix (Fin S.rank) (Fin S.rank) k) := by
    have h := FS.γβ
    rw [hγS, Matrix.smul_mul] at h
    rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r j
    set lam : k := q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * q.pr (incA D a) with hlam
    let M : Matrix (Fin T.rank) (Fin S.rank) k := Matrix.of fun i l => lam * q.pr (incA D (t i)) * q.pr (incA D (star (s l)))
    have hmap : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) :
        WO S T).map q.pr = M * Gw := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, M, hGw, tmul_eq, map_mul, map_sum, hlam]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hd : (Place.ofSplitPt q).down FS FT (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ l, star (s l) * S.gram l j)) = c⁻¹ • M := by
      have hπ : (Place.ofSplitPt q).π = q.pr := rfl
      simp only [Place.down, hπ]
      rw [hγT, Matrix.one_mul, hmap, Matrix.mul_assoc, hGβ, Matrix.mul_smul, Matrix.mul_one]
    rw [hd, Matrix.smul_apply, smul_eq_mul]
    have e : c⁻¹ * M r j = q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * (q.pr (incA D a) / c) *
        q.pr (incA D (t r)) * q.pr (incA D (star (s j))) := by
      simp only [M, Matrix.of_apply, hlam]; field_simp
    rw [e]
    refine mul_mem (mul_mem (mul_mem (GlobalTheory.SplitCharCond.pr_pair_int q hα) (hAA a ha)) ?_) ?_
    · exact pr_int_of_isIntegral q (ht r)
    · exact pr_int_of_isIntegral q (star_isIntegral (hs j))
  | zero =>
    intro r j
    have : (Place.ofSplitPt q).down FS FT 0 = 0 := map_zero (Witness.downH (Place.ofSplitPt q) FS FT)
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    intro r j
    rw [Witness.down_add, Matrix.add_apply]
    exact add_mem (hx r j) (hy r j)
  | neg x _ hx =>
    intro r j
    have : (Place.ofSplitPt q).down FS FT (-x) = -(Place.ofSplitPt q).down FS FT x :=
      map_neg (Witness.downH (Place.ofSplitPt q) FS FT) x
    rw [this, Matrix.neg_apply]
    exact neg_mem (hx r j)

end GlobalTheory.LocMod.StdHomDown
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdHomLatticePointIntegralMatrixAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdHomLattice_point_integral_matrix_at_split_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (c : k), c ≠ 0 → (∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / c ∈ 𝒪[k]) → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = c • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k] := by
  first | exact @GlobalTheory.LocMod.StdHomDown.down_mem_integer | exact GlobalTheory.LocMod.StdHomDown.down_mem_integer | (intros; apply GlobalTheory.LocMod.StdHomDown.down_mem_integer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHalfEqDoubleAnnihilator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HalfDoubleAnn

theorem frames_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D), ∃ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), (∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k]) ∧ (∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T) := by
  intro D k _ _ _ _ q S T
  obtain ⟨a₀, ha₀, hne, hdiv⟩ := GlobalTheory.T.exists_periodIdeal_local_generator_at_split_point D k q
  set c := q.pr (incA D a₀) with hc
  set G : Matrix (Fin S.rank) (Fin S.rank) k := c • (HSpace.gram S).map (fun a => q.pr (incA D a)) with hG
  have hdet : IsUnit G.det := by
    rw [hG, Matrix.det_smul, isUnit_iff_ne_zero]
    refine mul_ne_zero (pow_ne_zero _ hne) ?_
    have h := (RingHom.map_det (q.pr.comp (incA D)) (HSpace.gram S)).symm
    simp only [RingHom.mapMatrix_apply, RingHom.coe_comp] at h
    change (Matrix.map (HSpace.gram S) (⇑q.pr ∘ ⇑(incA D))).det ≠ 0
    rw [h]
    exact (map_ne_zero_iff _ (q.pr.comp (incA D)).injective).2 (GlobalTheory.FrameCont.gram_det_isUnit S).ne_zero
  let FS : Frame k S.rank (Fin S.rank) := ⟨G⁻¹, G, Matrix.nonsing_inv_mul G hdet, Matrix.mul_nonsing_inv G hdet⟩
  let FT : Frame k T.rank (Fin T.rank) := ⟨1, 1, mul_one 1, mul_one 1⟩
  exact ⟨FS, FT, GlobalTheory.T.stdHomLattice_point_integral_matrix_at_split_place D k q S T c hne hdiv FS FT rfl rfl rfl, GlobalTheory.T.integral_matrix_split_place_mem_stdHomLattice D k q S T a₀ ha₀ hne FS FT rfl rfl rfl⟩

variable {D : D7}

theorem symplO_idem_left (S T : HSp D) {e : AE D} {l : WO S T} (hl : IsHalf (cA D e) l) (u : WO S T) :
    symplO S T u l = symplO S T (u.map (e * ·)) l := by
  unfold symplO hO
  congr 2
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  have h : cA D (l c b) = e * cA D (l c b) := by
    conv_lhs => rw [← hl c b]
    rw [map_mul, cA_cA]
  rw [Matrix.map_apply]
  conv_lhs => rw [h]
  ring

theorem pr_e {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.pr q.e = 1 := by
  have h := q.sec_pr 1
  rw [mul_one] at h
  rw [← h, q.pr_sec, map_one]

theorem mul_idem_of_mem {E₂ : AE D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (hsum : E₂ = ∑ PP ∈ Q, es PP) {PP : Formalism.L2.DIV.Pl D.host.E}
    (hPP : PP ∈ Q) : E₂ * es PP = es PP := by
  rw [hsum, Finset.sum_mul, Finset.sum_eq_single PP]
  · exact (hes PP hPP).1.1
  · intro PP' hPP' hne
    have hs := (hes PP hPP).1
    obtain ⟨v, ε, h1, h2⟩ := hs.2.2
    obtain ⟨q, hq, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v (es PP) ε hs h1 h2
    have hsum' : IsIdemSum (es PP') {PP'} :=
      ⟨⟨fun _ => es PP', fun P hP => by rw [Finset.mem_singleton] at hP; subst hP; exact hes _ hPP', by simp⟩,
        (hes PP' hPP').1.2.1⟩
    have := OutsideOrth.mul_eq_zero D _ (Place.ofSplitPt q) {PP'} PP (es PP')
      (by rw [Finset.mem_singleton]; exact fun h => hne h.symm) (by rw [show (Place.ofSplitPt q).e = es PP from hq]; exact hes PP hPP) hsum'
    rwa [show (Place.ofSplitPt q).e = es PP from hq] at this
  · intro h; exact absurd hPP h

end GlobalTheory.HalfDoubleAnn

namespace GlobalTheory.HalfDoubleAnn
variable {D : D7}

theorem idem_part_mem (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (E₂ e : AE D)
    (he : IsSplitIdem D e) (hEe : E₂ * e = e) (x : WO S T)
    (H : ∀ y : WO S T, IsHalf (cA D E₂) y → (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) →
      ψ (symplO S T x y) = 1) :
    x.map (e * ·) ∈ stdHom S T := by
  obtain ⟨v, ε, h1, h2⟩ := he.2.2
  obtain ⟨q, hq, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he h1 h2
  subst hq
  obtain ⟨FS, FT, hF1, hF2⟩ := frames_stdHom D _ q S T
  obtain ⟨Λ, -, h2, -, h4, -, h6⟩ := GlobalTheory.SplitSelfDual.selfDual_lattice_split D _ (Place.ofSplitPt q) ψ hψ S T (Fin T.rank) (Fin S.rank) FS FT
  have hdown : ∀ u : WO S T, (Place.ofSplitPt q).down FS FT (u.map (q.e * ·)) = (Place.ofSplitPt q).down FS FT u := by
    intro u
    unfold Place.down
    congr 2
    ext i j
    simp only [Matrix.map_apply]
    have h1 : (Place.ofSplitPt q).π q.e = 1 := pr_e q
    rw [map_mul, h1, one_mul]
  have hhalf : ∀ u : WO S T, IsHalf q.e (u.map (q.e * ·)) := fun u i j => by
    rw [Matrix.map_apply, ← mul_assoc, he.1]
  set y := x.map (q.e * ·) with hy
  by_contra hyn
  have hyup : (Place.ofSplitPt q).up FS FT ((Place.ofSplitPt q).down FS FT y) = y := Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x)
  have hnint : ¬ ∀ r s, (Place.ofSplitPt q).down FS FT y r s ∈ 𝒪[_] := fun hint => hyn (hyup ▸ hF2 _ hint)
  have hyΛ : y ∉ Λ := fun hm => hnint ((h4 _).1 (hyup.symm ▸ hm))
  obtain ⟨l, hlΛ, hlc, hl⟩ := h2 y (hhalf x) hyΛ
  have hlc' : IsHalf (cA D q.e) l := hlc
  have hlE : IsHalf (cA D E₂) l := fun i j => by
    rw [← hlc' i j, ← mul_assoc, ← map_mul, hEe]
  have key := H l hlE fun x' hx' _ => by
    rw [symplO_idem_left S T hlc' x', ← Witness.up_down (Place.ofSplitPt q) FS FT (hhalf x'), hdown]
    exact h6 l hlΛ hlc _ (hF1 x' hx')
  rw [symplO_idem_left S T hlc' x, GlobalTheory.SplitScalar.symplO_skew] at key
  have := GlobalTheory.SplitSelfDual.psi_neg_eq_one key
  rw [neg_neg] at this
  exact hl this

theorem mem_of_ann_ann : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ x : WO S T, IsHalf E₂ x → (∀ y : WO S T, IsHalf (cA D E₂) y → (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) → ψ (symplO S T x y) = 1) → x ∈ stdHom S T := by
  intro D ψ hψ S T Q E₂ hE x hx H
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hE
  have hx' : x = ∑ PP ∈ Q, x.map (es PP * ·) := by
    ext i j
    rw [Matrix.sum_apply, ← hx i j, hsum, Finset.sum_mul]
    rfl
  rw [hx']
  exact AddSubgroup.sum_mem _ fun PP hPP =>
    idem_part_mem ψ hψ S T E₂ (es PP) (hes PP hPP).1 (mul_idem_of_mem hes hsum hPP) x H

end GlobalTheory.HalfDoubleAnn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHalfEqDoubleAnnihilatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_lattice_half_eq_double_annihilator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ x : WO S T, IsHalf E₂ x → (∀ y : WO S T, IsHalf (cA D E₂) y → (∀ x' ∈ stdHom S T, IsHalf E₂ x' → ψ (symplO S T x' y) = 1) → ψ (symplO S T x y) = 1) → x ∈ stdHom S T := by
  first | exact @GlobalTheory.HalfDoubleAnn.mem_of_ann_ann | exact GlobalTheory.HalfDoubleAnn.mem_of_ann_ann | (intros; apply GlobalTheory.HalfDoubleAnn.mem_of_ann_ann <;> assumption)
end
