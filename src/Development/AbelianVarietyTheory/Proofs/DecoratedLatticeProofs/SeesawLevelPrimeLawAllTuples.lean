module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumChangeAtSplitPlacesProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCombinationExtendByZeroOrthSumLine
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepSmallPairsValueAllGluedSplitPlacesProo
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeLawLastTwoStepsAllTuples

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLevelPrimeLawDoubleStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeOrthogonalSumLineAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeOrthogonalSumLineAtSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineSplitAt
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem mulVec_sec {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (u : Fin n → k) :
    M *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((M.map p.pr *ᵥ u) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, FrameLat.sec_mul_right, mul_comm (u j)]

theorem mulVec_csec {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (z : Fin n → k) :
    M *ᵥ (fun i => cA D (p.sec (z i))) = fun i => cA D (p.sec ((M.map (fun a => p.pr (cA D a)) *ᵥ z) i)) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FrameLat.sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, FrameLat.e_mul_sec, map_mul, Formalism.L2.Theta.cA_cA]

theorem eq_sec_add_csec {n : ℕ} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (· = p.v)) :
    y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
  funext i
  have h := (FrameLat.idem_iff p (y i)).1 (hy i)
  simp only [Pi.add_apply, p.sec_pr, map_mul, Formalism.L2.Theta.cA_cA]
  rw [← add_mul, h]

variable {p}

theorem mulVec_mem_of_parts {S T : HSp D} {L : Lat S} {L' : Lat T} (hL : IsSelfDualC S L)
    (M : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    (hw : ∀ u, (fun i => p.sec (u i)) ∈ latV S L (· = p.v) → (fun i => p.sec ((M.map p.pr *ᵥ u) i)) ∈ latV T L' (· = p.v))
    (hc : ∀ z, (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) →
      (fun i => cA D (p.sec ((M.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV T L' (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = p.v)) : M *ᵥ y ∈ latV T L' (· = p.v) := by
  have e := eq_sec_add_csec p (FrameLat.latV_supp hy)
  rw [e] at hy ⊢
  have h := (FrameLat.decomp hL _ _).1 hy
  rw [Matrix.mulVec_add, mulVec_sec, mulVec_csec]
  exact add_mem (hw _ h.1) (hc _ h.2)

theorem pair_eq (S : HSp D) (x z : Fin S.rank → k) :
    ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j =
      x ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, RingHom.comp_apply, mul_assoc]

theorem conjT_map {m n : Type} (M : Matrix m n D.host.E) :
    Mᴴ.map (p.pr.comp ((cA D).comp (incA D))) = (M.map (p.pr.comp (incA D)))ᵀ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, RingHom.comp_apply, FrameLat.cA_incA,
    star_star]

end GlobalTheory.LineSplitAt

namespace GlobalTheory.LineSplitAt


set_option maxHeartbeats 1000000 in
theorem orthAt_of_frames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n' : Type) [Fintype n'] [DecidableEq n'] (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → p.UnitAA → ∀ (LA : Lat A) (LS : Lat S) (ΛA : Submodule 𝒪[k] (n' → k)), IsSelfDualC A LA → IsSelfDualC S LS → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → ∃ LL : Lat L, OrthAt o LS LA LL p.v := by
  intro D k _ _ _ _ p n' _ _ S A L o ζ _ α α₀ hsum _ LA LS ΛA hLA hLS hα hα₀
  have hb : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hsum
  have hPJ : o.pA.map p.pr * o.jA.map p.pr = 1 := by
    rw [← Matrix.map_mul, o.pA_jA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hz : o.pA.map p.pr *ᵥ (⇑p.pr ∘ ratV (vecB o ζ)) = 0 := by
    have e1 : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ratV, vecB, OrthDec.jB, rat, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    funext i
    rw [← RingHom.map_mulVec, e1, Matrix.mulVec_mulVec, o.pA_jB, Matrix.zero_mulVec]
    simp
  have hPz : o.pA.map p.pr * replicateCol (Fin 1) (fun i => p.pr (ratV (vecB o ζ) i)) = 0 := by
    ext i j
    have := congrFun hz i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

  have hwA : ∀ u : Fin A.rank → k, (fun i => p.sec (u i)) ∈ latV A LA (· = p.v) →
      (fun i => p.sec ((o.jA.map p.pr *ᵥ u) i)) ∈ latV S LS (· = p.v) := by
    intro u hu
    have hx : α.b' *ᵥ u ∈ ΛA := (hα _).2 (by rwa [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec])
    have e : o.jA.map p.pr *ᵥ u = α₀.b *ᵥ Sum.elim (α.b' *ᵥ u) 0 := by
      rw [hb, Matrix.fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_mulVec, Matrix.mul_assoc, α.bb',
        Matrix.mul_one, Matrix.mulVec_zero, add_zero]
    rw [e]
    exact (hα₀ _).1 (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using hx, by simp⟩)
  have hwS : ∀ u : Fin S.rank → k, (fun i => p.sec (u i)) ∈ latV S LS (· = p.v) →
      (fun i => p.sec ((o.pA.map p.pr *ᵥ u) i)) ∈ latV A LA (· = p.v) := by
    intro u hu
    have hy : α₀.b' *ᵥ u ∈ lastKer ΛA := (hα₀ _).2 (by rwa [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec])
    have e : o.pA.map p.pr *ᵥ u = α.b *ᵥ ((α₀.b' *ᵥ u) ∘ Sum.inl) := by
      conv_lhs => rw [← Matrix.one_mulVec u, ← α₀.bb', ← Matrix.mulVec_mulVec, hb, Matrix.fromCols_mulVec, Matrix.mulVec_add,
        Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPJ, Matrix.one_mul, Matrix.mulVec_mulVec _ (o.pA.map p.pr), hPz,
        Matrix.zero_mulVec, add_zero]
    rw [e]
    exact (hα _).1 (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy).1

  have hG2 : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  have hG1 : S.gram * o.iA = o.qAᴴ * A.gram := by
    have := congrArg Matrix.conjTranspose hG2
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, gram_conjTranspose] at this
    exact this.symm
  have hcA : ∀ z : Fin A.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV A LA (· = p.v) →
      (fun i => cA D (p.sec ((o.jA.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV S LS (· = p.v) := by
    intro z hz
    refine (FrameLat.csec_mem_iff hLS _).2 fun x hx => ?_
    have key : ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * (o.jA.map (fun a => p.pr (cA D a)) *ᵥ z) j =
        ∑ i, ∑ j, (o.pA.map p.pr *ᵥ x) i * p.pr (cA D (incA D (A.gram i j))) * z j := by
      rw [pair_eq, pair_eq]
      change x ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ (o.iA.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)) =
        (o.qA.map (p.pr.comp (incA D)) *ᵥ x) ⬝ᵥ (A.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hG1, Matrix.map_mul, conjT_map, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [key]
    exact (FrameLat.csec_mem_iff hLA z).1 hz _ (hwS x hx)
  have hcS : ∀ z : Fin S.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV S LS (· = p.v) →
      (fun i => cA D (p.sec ((o.pA.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV A LA (· = p.v) := by
    intro z hz
    refine (FrameLat.csec_mem_iff hLA _).2 fun x hx => ?_
    have key : ∑ i, ∑ j, x i * p.pr (cA D (incA D (A.gram i j))) * (o.pA.map (fun a => p.pr (cA D a)) *ᵥ z) j =
        ∑ i, ∑ j, (o.jA.map p.pr *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * z j := by
      rw [pair_eq, pair_eq]
      change x ⬝ᵥ (A.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ (o.qA.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)) =
        (o.iA.map (p.pr.comp (incA D)) *ᵥ x) ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hG2, Matrix.map_mul, conjT_map, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [key]
    exact (FrameLat.csec_mem_iff hLS z).1 hz _ (hwA x hx)
  have h1 : ∀ y ∈ latV A LA (· = p.v), o.jA *ᵥ y ∈ latV S LS (· = p.v) := fun y hy =>
    mulVec_mem_of_parts hLA o.jA hwA hcA hy
  have h2 : ∀ y ∈ latV S LS (· = p.v), o.pA *ᵥ y ∈ latV A LA (· = p.v) := fun y hy =>
    mulVec_mem_of_parts hLS o.pA hwS hcS hy
  have hsplit : ∀ g : Fin S.rank → AE D, o.jA *ᵥ (o.pA *ᵥ g) + o.jB *ᵥ (o.pB *ᵥ g) = g := fun g => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  let fB := (mulVecLin o.qB).restrictScalars (𝓞 D.host.E)
  have h3 : ∀ x ∈ latV L (LS.map fB) (· = p.v), o.jB *ᵥ x ∈ latV S LS (· = p.v) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, ha', c, hc, w, hw, rfl⟩ := hx
      rw [Set.mem_singleton_iff] at hc
      subst hc
      obtain ⟨s, hs, rfl⟩ := hw
      have hg : (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i)) ∈ latV S LS (· = p.v) :=
        AddSubgroup.subset_closure ⟨a, ha, ha', 1, rfl, s, hs, rfl⟩
      have e2 : o.pB *ᵥ (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i)) =
          fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * (o.qB *ᵥ s) i) := by
        funext i
        simp only [Matrix.mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] o.qB i j) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      show o.jB *ᵥ (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * (o.qB *ᵥ s) i)) ∈ _
      rw [← e2]
      have hm := hg
      rw [← hsplit (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i))] at hm
      exact (add_mem_cancel_left (h1 _ (h2 _ hg))).1 hm
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx
  refine ⟨LS.map fB, fun y => ⟨fun hy => ⟨h2 y hy, GlobalTheory.OrthSumLat.rat_mulVec_mem_latV o.qB
    (fun x hx => Submodule.mem_map_of_mem hx) hy⟩, fun h => ?_⟩⟩
  rw [← hsplit y]
  exact add_mem (h1 _ h.1) (h3 _ h.2)

end GlobalTheory.LineSplitAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeOrthogonalSumLineAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_orthogonal_sum_line_at_split_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n' : Type) [Fintype n'] [DecidableEq n'] (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → p.UnitAA → ∀ (LA : Lat A) (LS : Lat S) (ΛA : Submodule 𝒪[k] (n' → k)), IsSelfDualC A LA → IsSelfDualC S LS → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → ∃ LL : Lat L, OrthAt o LS LA LL p.v := by
  first | exact @GlobalTheory.LineSplitAt.orthAt_of_frames | exact GlobalTheory.LineSplitAt.orthAt_of_frames | (intros; apply GlobalTheory.LineSplitAt.orthAt_of_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProof
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl.ExtZero

namespace GlobalTheory.FinPl.ExtAllPf

variable {D : D7}

theorem vac_zero' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} (P : Pl D → Prop) :
    Vac ψ S T LS LT P 0 := by
  have h : ∀ u, heisO ψ S T u 0 = 0 := fun u => by funext w; simp [heisO]
  exact ⟨⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun u _ _ => h u⟩, continuous_const, fun _ _ _ _ _ => contDiff_const⟩,
    fun u _ => h _, fun _ _ u _ _ => h u⟩

theorem vac_at' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {v : Pl D}
    {f : WO S T → ℂ} (hv : P v) (h : Vac ψ S T LS LT P f) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hz, rest⟩
    exact ⟨α, hα, fun v' hv' => hz v' (fun e => hv' (by subst e; exact hv)), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem idAt_mono' {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) : idAt D P ≤ idAt D Q := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

theorem combAt_extS {P : Pl D → Prop} {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {c : WO A T →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extS o T c) := by
  classical
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hc x hx i k)

theorem combAt_extT {P : Pl D → Prop} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {c : WO S A →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extT o S c) := by
  classical
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hc x hx k j)

theorem comb_eq_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (F : WO S T → ℂ) :
    comb ψ S T c F = c.sum (fun u a => a • heisO ψ S T u F) := rfl

theorem comb_extS_slice (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (c : WO A T →₀ ℂ)
    (F : WO S T → ℂ) (w : WO A T) (y : WO L T) :
    comb ψ S T (extS o T c) F ((o.resS T).symm (w, y)) = comb ψ A T c (fun w' => F ((o.resS T).symm (w', y))) w := by
  rw [comb_eq_sum, comb_eq_sum, extS, Finsupp.sum_mapDomain_index (h := fun u a => a • heisO ψ S T u F) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [heisO_resS_symm]

theorem comb_extT_slice (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (c : WO T A →₀ ℂ)
    (F : WO T S → ℂ) (w : WO T A) (y : WO T L) :
    comb ψ T S (extT o T c) F ((o.resT T).symm (w, y)) = comb ψ T A c (fun w' => F ((o.resT T).symm (w', y))) w := by
  rw [comb_eq_sum, comb_eq_sum, extT, Finsupp.sum_mapDomain_index (h := fun u a => a • heisO ψ T S u F) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [heisO_resT_symm]

section Lists

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem overAll_sb {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S} {LT : Lat T}
    {Ψ : ι → Matrix n n' k → ℂ} : ∀ (l : List ι) (f f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ l f f' →
      ∀ i ∈ l, Ψ i ∈ SB (Matrix n n' k) := by
  intro l
  induction l with
  | nil => intro f f' _ i hi; simp at hi
  | cons j l ih =>
    intro f f' h i hi
    obtain ⟨g, hg, hO⟩ := h
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hO.2.2.2.1
    · exact ih f g hg i hi

def chainOp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : ι → WO S T →₀ ℂ) (l : List ι) (f : WO S T → ℂ) :
    WO S T → ℂ :=
  l.foldr (fun i g => comb ψ S T (e i) g) f

theorem chainOp_vac {LS : Lat S} {LT : Lat T} (e : ι → WO S T →₀ ℂ)
    (hpres : ∀ i j, i ≠ j → ∀ g, Vac ψ S T LS LT (· = (p j).v) g → Vac ψ S T LS LT (· = (p j).v) (comb ψ S T (e i) g)) :
    ∀ (l : List ι) (f : WO S T → ℂ), (∀ i, Vac ψ S T LS LT (· = (p i).v) f) →
      ∀ j, j ∉ l → Vac ψ S T LS LT (· = (p j).v) (chainOp ψ S T e l f) := by
  intro l
  induction l with
  | nil => intro f hf j _; exact hf j
  | cons i l ih =>
    intro f hf j hj
    have hij : i ≠ j := fun h => hj (h ▸ List.mem_cons_self)
    exact hpres i j hij _ (ih f hf j fun h => hj (List.mem_cons_of_mem _ h))

theorem overAll_chain (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T)
    (Φ : ι → Matrix n n' k → ℂ) (e : ι → WO S T →₀ ℂ)
    (hE : ∀ i f₀, Vac ψ S T LS LT (· = (p i).v) f₀ → Over ψ (α i) (β i) LS LT f₀ (Φ i) (comb ψ S T (e i) f₀))
    (hpres : ∀ i j, i ≠ j → ∀ g, Vac ψ S T LS LT (· = (p j).v) g → Vac ψ S T LS LT (· = (p j).v) (comb ψ S T (e i) g)) :
    ∀ (l : List ι), l.Nodup → ∀ f, (∀ i, Vac ψ S T LS LT (· = (p i).v) f) →
      OverAll ψ α β LS LT Φ l f (chainOp ψ S T e l f) := by
  intro l
  induction l with
  | nil => intro _ f _; rfl
  | cons i l ih =>
    intro hl f hf
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    exact ⟨chainOp ψ S T e l f, ih hl' f hf, hE i _ (chainOp_vac e hpres l f hf i hi)⟩

set_option maxHeartbeats 1000000 in
theorem pres_of_allComb (hAC : AllComb D) {I : List ι} {P : Pl D → Prop} (hP : Places p I P)
    (hψ : IsStdChar D ψ (-1)) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (e : ι → WO S T →₀ ℂ) (he : ∀ i, CombAt (· = (p i).v) (e i)) :
    ∀ i j, i ≠ j → ∀ g, Vac ψ S T LS LT (· = (p j).v) g → Vac ψ S T LS LT (· = (p j).v) (comb ψ S T (e i) g) := by
  intro i j hij g hg
  have hPl : Places (fun _ : Unit => p j) [()] (· = (p j).v) :=
    ⟨List.nodup_singleton _, fun _ => List.mem_singleton.2 rfl, fun a b _ => Subsingleton.elim a b,
      fun x => ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩, fun _ => hP.unit j⟩
  have hc : CombAt (fun x => ¬ (x = (p j).v)) (e i) := by
    intro u hu a b
    have h1 := he i u hu a b
    exact idAt_mono' (P := (· = (p i).v)) (Q := fun x => ¬ (x = (p j).v))
      (fun v hv hvj => hij (hP.inj (show (p i).v = (p j).v from hv.symm.trans hvj))) h1
  exact ((hAC k Unit (fun _ => p j) [()] (· = (p j).v) hPl n n' ψ hψ S T (fun _ => α j) (fun _ => β j) LS LT hS hT
    (fun _ => 0)).2.2 (e i) hc g hg).1

end Lists

theorem chainOp_sliceS (ψ : AddChar (AF D.host.F) ℂ) {ι : Type} {S A L T : HSp D} (o : OrthDec S A L)
    (d : ι → WO A T →₀ ℂ) (y : WO L T) : ∀ (l : List ι) (h : WO S T → ℂ) (w : WO A T),
    chainOp ψ S T (fun i => extS o T (d i)) l h ((o.resS T).symm (w, y)) =
      chainOp ψ A T d l (fun w' => h ((o.resS T).symm (w', y))) w := by
  intro l
  induction l with
  | nil => intro h w; rfl
  | cons i l ih =>
    intro h w
    simp only [chainOp, List.foldr_cons] at ih ⊢
    rw [comb_extS_slice]
    exact congrArg (fun F => comb ψ A T (d i) F w) (funext fun w' => ih h w')

theorem chainOp_sliceT (ψ : AddChar (AF D.host.F) ℂ) {ι : Type} {S A L T : HSp D} (o : OrthDec S A L)
    (d : ι → WO T A →₀ ℂ) (y : WO T L) : ∀ (l : List ι) (h : WO T S → ℂ) (w : WO T A),
    chainOp ψ T S (fun i => extT o T (d i)) l h ((o.resT T).symm (w, y)) =
      chainOp ψ T A d l (fun w' => h ((o.resT T).symm (w', y))) w := by
  intro l
  induction l with
  | nil => intro h w; rfl
  | cons i l ih =>
    intro h w
    simp only [chainOp, List.foldr_cons] at ih ⊢
    rw [comb_extT_slice]
    exact congrArg (fun F => comb ψ T A (d i) F w) (funext fun w' => ih h w')

theorem vac_sliceS {ψ : AddChar (AF D.host.F) ℂ} {S A L T : HSp D} (o : OrthDec S A L) {P : Pl D → Prop}
    {LA : Lat A} {LS : Lat S} {LT : Lat T} (hA : IsSelfDualC A LA) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hO : ∀ v, P v → ∃ LL, OrthAt o LS LA LL v) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) (y : WO L T) :
    Vac ψ A T LA LT P (fun w => f ((o.resS T).symm (w, y))) := by
  have latS := GlobalTheory.ContrComb.extL_mem_latO D S A L T o P LA LT LS hA hT hS hO
  refine ⟨GlobalTheory.T.isThetaFunO_source_slice D ψ S A L T o f y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · funext w
    rw [← heisO_resS_symm ψ o (2 • u) f w y]
    have h2 : (o.resS T).symm (2 • u, 0) = 2 • (o.resS T).symm (u, 0) := by
      rw [← map_nsmul]; simp
    rw [h2, hf.2.1 _ (latS u hu)]
  · funext w
    rw [← heisO_resS_symm ψ o u f w y, hf.2.2 e' he' _ (latS u hu) (half_resS_symm o hh)]

theorem vac_sliceT {ψ : AddChar (AF D.host.F) ℂ} {S A L T : HSp D} (o : OrthDec S A L) {P : Pl D → Prop}
    {LA : Lat A} {LS : Lat S} {LT : Lat T} (hA : IsSelfDualC A LA) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hO : ∀ v, P v → ∃ LL, OrthAt o LS LA LL v) {f : WO T S → ℂ} (hf : Vac ψ T S LT LS P f) (y : WO T L) :
    Vac ψ T A LT LA P (fun w => f ((o.resT T).symm (w, y))) := by
  have latT := GlobalTheory.ContrComb.LatT.latO_extR D S A L T o P LA LT LS hA hT hS hO
  refine ⟨GlobalTheory.T.isThetaFunO_target_slice_orthogonal_sum D ψ S A L T o f y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · funext w
    rw [← heisO_resT_symm ψ o (2 • u) f w y]
    have h2 : (o.resT T).symm (2 • u, 0) = 2 • (o.resT T).symm (u, 0) := by
      rw [← map_nsmul]; simp
    rw [h2, hf.2.1 _ (latT u hu)]
  · funext w
    rw [← heisO_resT_symm ψ o u f w y, hf.2.2 e' he' _ (latT u hu) (half_resT_symm o hh)]

end GlobalTheory.FinPl.ExtAllPf

namespace GlobalTheory.FinPl.ExtAllPf


set_option maxHeartbeats 2000000 in
theorem ext_all : ∀ D : D7, GlobalTheory.FinPl.ExtAll D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ ψ hψ S A L T o ζ hζ α α₀ β hsum LA LS LT ΛA ΛT hA hS hT hlat
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D
  have hO : ∀ x, P x → ∃ LL, OrthAt o LS LA LL x := by
    intro x hx
    obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
    exact GlobalTheory.T.lattice_orthogonal_sum_line_at_split_place D k (p i) n' S A L o ζ hζ (α i) (α₀ i) (hsum i) (hP.unit i) LA LS (ΛA i) hA hS (hlat i).1
      (hlat i).2.1
  have hv : ∀ {U V : HSp D} {LU : Lat U} {LV : Lat V} {f : WO U V → ℂ}, Vac ψ U V LU LV P f →
      ∀ i, Vac ψ U V LU LV (· = (p i).v) f := fun hf i => vac_at' ((hP.mem _).2 ⟨i, rfl⟩) hf
  refine ⟨hO, fun Ψ c hc => ?_, fun Ψ c hc => ?_⟩
  · have hSB : ∀ i, Ψ i ∈ SB (Matrix n n' k) := fun i => overAll_sb I 0 _ (hc.2 0 (vac_zero' P)) i (hP.all i)
    choose d hd using fun i => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ (hP.unit i) A T (α i) (β i) LA LA LT LT hA hT hA
      hT).2 (Ψ i) (hSB i)
    have hext : ∀ i f₀, Vac ψ S T LS LT (· = (p i).v) f₀ → Over ψ (α₀ i) (β i) LS LT f₀ (tensCol (Ψ i) (vecInd (ΛT i)))
        (comb ψ S T (extS o T (d i)) f₀) := fun i => (GlobalTheory.T.splitPlace_combination_extendByZero_orthSum_line D k (p i) n n' ψ hψ (hP.unit i) S A L T o ζ hζ (α i)
      (α₀ i) (β i) (hsum i) LA LS LT (ΛA i) (ΛT i) hA hS hT (hlat i).1 (hlat i).2.1 (hlat i).2.2).1 (Ψ i) (d i) (hd i).1
      (hd i).2
    have presA := pres_of_allComb hAC hP hψ α β hA hT d (fun i => (hd i).1)
    have presS := pres_of_allComb hAC hP hψ α₀ β hS hT (fun i => extS o T (d i)) (fun i => combAt_extS o T (hd i).1)
    refine ⟨combAt_extS o T hc.1, fun f hf => ?_⟩
    have key : comb ψ S T (extS o T c) f = chainOp ψ S T (fun i => extS o T (d i)) I f := by
      funext t
      obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resS T).symm q = t := ⟨_, (o.resS T).symm_apply_apply t⟩
      rw [comb_extS_slice, chainOp_sliceS]
      have hfy := vac_sliceS o hA hS hT hO hf y
      have := (hAC k ι p I P hP n n' ψ hψ A T α β LA LT hA hT Ψ).2.1 _ _ _ (hc.2 _ hfy)
        (overAll_chain α β LA LT Ψ d (fun i => (hd i).2) presA I hP.nodup _ (hv hfy))
      exact congrFun this w
    rw [key]
    exact overAll_chain α₀ β LS LT _ _ hext presS I hP.nodup f (hv hf)
  · have hSB : ∀ i, Ψ i ∈ SB (Matrix n' n k) := fun i => overAll_sb I 0 _ (hc.2 0 (vac_zero' P)) i (hP.all i)
    choose d hd using fun i => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n' n ψ hψ (hP.unit i) T A (β i) (α i) LT LT LA LA hT hA hT
      hA).2 (Ψ i) (hSB i)
    have hext : ∀ i f₀, Vac ψ T S LT LS (· = (p i).v) f₀ → Over ψ (β i) (α₀ i) LT LS f₀ (tensRow (Ψ i) (dualInd (ΛT i)))
        (comb ψ T S (extT o T (d i)) f₀) := fun i => (GlobalTheory.T.splitPlace_combination_extendByZero_orthSum_line D k (p i) n n' ψ hψ (hP.unit i) S A L T o ζ hζ (α i)
      (α₀ i) (β i) (hsum i) LA LS LT (ΛA i) (ΛT i) hA hS hT (hlat i).1 (hlat i).2.1 (hlat i).2.2).2 (Ψ i) (d i) (hd i).1
      (hd i).2
    have presA := pres_of_allComb hAC hP hψ β α hT hA d (fun i => (hd i).1)
    have presS := pres_of_allComb hAC hP hψ β α₀ hT hS (fun i => extT o T (d i)) (fun i => combAt_extT o T (hd i).1)
    refine ⟨combAt_extT o T hc.1, fun f hf => ?_⟩
    have key : comb ψ T S (extT o T c) f = chainOp ψ T S (fun i => extT o T (d i)) I f := by
      funext t
      obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resT T).symm q = t := ⟨_, (o.resT T).symm_apply_apply t⟩
      rw [comb_extT_slice, chainOp_sliceT]
      have hfy := vac_sliceT o hA hS hT hO hf y
      have := (hAC k ι p I P hP n' n ψ hψ T A β α LT LA hT hA Ψ).2.1 _ _ _ (hc.2 _ hfy)
        (overAll_chain β α LT LA Ψ d (fun i => (hd i).2) presA I hP.nodup _ (hv hfy))
      exact congrFun this w
    rw [key]
    exact overAll_chain β α₀ LT LS _ _ hext presS I hP.nodup f (hv hf)

end GlobalTheory.FinPl.ExtAllPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionByZeroAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.ExtAll D := by
  first | exact @GlobalTheory.FinPl.ExtAllPf.ext_all | exact GlobalTheory.FinPl.ExtAllPf.ext_all | (intros; apply GlobalTheory.FinPl.ExtAllPf.ext_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLevelPrimeLawDoubleStep
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPrimeMid

variable {D : D7}

theorem mxAt_mul_right (P : Pl D → Prop) {m n r : ℕ} {x : Mx D m n} (hx : MxAt P x) (M : Matrix (Fin n) (Fin r) (AE D)) :
    MxAt P (x * M) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem mxAt_mul_left (P : Pl D → Prop) {m n r : ℕ} {x : Mx D n r} (hx : MxAt P x) (M : Matrix (Fin m) (Fin n) (AE D)) :
    MxAt P (M * x) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem combAt_extS (P : Pl D → Prop) {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {c : WO A T →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extS o T c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  change (w ⬝ o.pA + (0 : WO L T) ⬝ o.pB) i j ∈ idAt D P
  rw [Matrix.zero_mul, add_zero]
  exact mxAt_mul_right P (hc w hw) _ i j

theorem combAt_extT (P : Pl D → Prop) {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {c : WO S A →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extT o S c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  change (o.jA ⬝ w + o.jB ⬝ (0 : WO S L)) i j ∈ idAt D P
  rw [Matrix.mul_zero, add_zero]
  exact mxAt_mul_left P (hc w hw) _ i j

theorem isFinComb_of_combAt (P : Pl D → Prop) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  exact (RingHom.mem_ker).1 (Ideal.mem_inf.1 (hc u hu i j)).1

theorem places_of_preT {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} {o : TDat c k ι} (H : PreT v o) : Places o.p o.I (· ∈ v.tP) :=
  ⟨H.nodup, H.all, H.inj, fun x => H.tP x, fun i => (H.char i).2⟩

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u (fun _ => 0) = fun _ => 0 := by
  funext w
  simp [heisO]

theorem vac_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) :
    Vac ψ S T LS LT P (fun _ => 0) :=
  ⟨GlobalTheory.OrientedHeis.theta_zero, fun u _ => heisO_zero ψ S T _, fun _ _ u _ _ => heisO_zero ψ S T u⟩

theorem biVacAt_zero (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (LA : Lat A) (LS : Lat S) (LA' : Lat A')
    (P : Pl D → Prop) : BiVacAt ψ LA LS LA' P (fun _ _ => 0) :=
  ⟨fun _ => vac_zero ψ A S LA LS P, fun _ => vac_zero ψ S A' LS LA' P⟩

theorem comb_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : comb ψ S T c (fun _ => 0) = fun _ => 0 := by
  funext w
  simp [comb, heisO_zero]

theorem biComb_zero (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    biComb ψ A S A' c c' (fun _ _ => 0) = fun _ _ => 0 := by
  funext u v
  simp only [biComb, comb_zero]

theorem biLift_zero {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) :
    biLift oma omb vA vS φ (fun _ _ => 0) = 0 := by
  funext h₂
  simp only [biLift]
  have e1 : ∀ h₀ h₁, (fun v : WO S A' => oma (h₀, h₁) (fun _ => 0) 0) = 0 := fun h₀ h₁ => by
    funext v; exact congrFun (map_zero (oma (h₀, h₁))) 0
  simp only [e1, map_zero, Pi.zero_apply, mul_zero, MeasureTheory.integral_zero]

end GlobalTheory.LevPrimeMid

namespace GlobalTheory.LevPrimeMid

variable {D : D7}

theorem bl_contr (hCL : ContrLaw D) {c : Comm D} (v : VCom c) (t : Tup c) (hW : WeilOK (t := t) v) {j σ : ℕ}
    (h : j + 2 * (σ + 1) + 2 = D.R.m) {φ : GA D (c.X j) → ℂ} (hφ : IsContAut (c.X j) φ)
    {Ξ₁ : WO (c.B j (σ + 1) h).V₀ (c.X (j + 1)) → ℂ} {Ξ₂ : WO (c.X (j + 1)) (c.B (j + 1 + 1) σ (idx_step h)).V₀ → ℂ}
    (h₁ : IsThetaFunO c.ψ _ _ Ξ₁) (h₂ : IsThetaFunO c.ψ _ _ Ξ₂) :
    c.bl j (t.kom j) (t.kom (j + 1)) φ (GlobalTheory.Unf.contr (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) Ξ₁ Ξ₂) =
      hand0 (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) φ Ξ₁ Ξ₂ := by
  obtain ⟨χA, χA', χz, omz, omz', e1, e2, w1, w2, w3, w4⟩ := hW.mid j σ h
  funext g
  have := (hCL c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) χA χA' χz (t.kom j) omz
    (t.kom (j + 1)) omz' e1 e2 w1 w2 w3 w4 φ Ξ₁ Ξ₂ hφ h₁ h₂).2.2 g
  rw [hand0, this]
  rfl

end GlobalTheory.LevPrimeMid

namespace GlobalTheory.LevPrimeMid

variable {D : D7}

theorem lastKer_isLattice {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
    (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : (lastKer L).IsLattice k := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer_eq q]
  refine Submodule.IsLattice.of_fg k ?_
  refine (((Submodule.IsLattice.fg k L |>.map _).sup (Submodule.fg_span_singleton _)).sup
      (Submodule.fg_span ?_)).sup (Submodule.fg_span ?_)
  · exact ((Set.finite_le_nat 1).image (avec k n 1)).subset fun _ ⟨i, _, _, h, e⟩ => ⟨i, h, e.symm⟩
  · exact ((Set.finite_le_nat 1).image (q.inv • avec k n 1 ·)).subset fun _ ⟨i, _, h, e⟩ => ⟨i, h, e.symm⟩

end GlobalTheory.LevPrimeMid

namespace GlobalTheory.LevPrimeMid

theorem lawLevelPrime_double : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) = o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)))) := by
  intro D c v k _ _ _ _ ι o hc hv hS j σ h
  have hPl := places_of_preT hS.pre
  obtain ⟨x₀⟩ := Formalism.L2.Col.nonempty_places D.host.F
  have hstd := hc.std
  have sd0 : IsSelfDualC _ (c.x j).L := (hc.x j (by omega)).sd
  have sd1 : IsSelfDualC _ (c.x (j + 1)).L := (hc.x (j + 1) (by omega)).sd
  have sd2 : IsSelfDualC _ (c.x (j + 1 + 1)).L := (hc.x (j + 1 + 1) (by omega)).sd
  have sdG : IsSelfDualC _ (o.M j (σ + 1) h) := ((hS.good x₀).bf j (σ + 1) h).sdV₀
  have sdG' : IsSelfDualC _ (o.M (j + 1 + 1) σ (idx_step h)) := ((hS.good x₀).fb j σ h).sdW₀
  obtain ⟨M0, sdM0, latM0, -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι o.p o.I _ hPl _ _ (o.β₀ j (σ + 1) h) (o.M j (σ + 1) h) sdG
    (fun i => lastKer (o.Q j i).lat) (fun i => by rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer_eq o.q]; exact gluedLat_isLattice o.q 1 2 _ 0)
  obtain ⟨M0', sdM0', latM0', -⟩ := GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces D k ι o.p o.I _ hPl _ _ (o.β₀ (j + 1 + 1) σ (idx_step h))
    (o.M (j + 1 + 1) σ (idx_step h)) sdG' (fun i => lastKer (o.Q (j + 1 + 1) i).lat) (fun i => by rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer_eq o.q]; exact gluedLat_isLattice o.q 1 2 _ 0)
  obtain ⟨e1, e1', he1, he1', hR1⟩ := GlobalTheory.T.vacuumChangeAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1)
    c.ψ hstd _ _ (o.β₀ j (σ + 1) h) (o.β (j + 1)) (o.M j (σ + 1) h) M0 (c.x (j + 1)).L (c.x (j + 1)).L sdG sd1 sdM0 sd1
  obtain ⟨e2, e2', he2, he2', hR2⟩ := GlobalTheory.T.vacuumChangeAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1 + 1)).rank ⊕ Fin 1)
    (Fin (c.X (j + 1)).rank) c.ψ hstd _ _ (o.β (j + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) (c.x (j + 1)).L (c.x (j + 1)).L
    (o.M (j + 1 + 1) σ (idx_step h)) M0' sd1 sdG' sd1 sdM0'

  have hext1 := GlobalTheory.T.extensionByZeroAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ hstd
    (c.bes j (σ + 1) h).V₀ (c.X j) (c.bes j (σ + 1) h).L (c.X (j + 1)) (c.bes j (σ + 1) h).o (c.bes j (σ + 1) h).ζ
    (c.bes j (σ + 1) h).line (o.β j) (o.β₀ j (σ + 1) h) (o.β (j + 1)) (fun i => (hS.glued j (σ + 1) h i).sum)
    (c.x j).L M0 (c.x (j + 1)).L (fun i => (o.Q j i).lat) (fun i => (o.Q (j + 1) i).lat) sd0 sdM0 sd1
    (fun i => ⟨hS.pre.latT j (by omega) i, latM0 i, hS.pre.latT (j + 1) (by omega) i⟩)
  have hext2 := GlobalTheory.T.extensionByZeroAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X (j + 1 + 1)).rank) c.ψ hstd
    (c.bes (j + 1 + 1) σ (idx_step h)).V₀ (c.X (j + 1 + 1)) (c.bes (j + 1 + 1) σ (idx_step h)).L (c.X (j + 1))
    (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ (c.bes (j + 1 + 1) σ (idx_step h)).line
    (o.β (j + 1 + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) (o.β (j + 1)) (fun i => (hS.glued (j + 1 + 1) σ (idx_step h) i).sum)
    (c.x (j + 1 + 1)).L M0' (c.x (j + 1)).L (fun i => (o.Q (j + 1 + 1) i).lat) (fun i => (o.Q (j + 1) i).lat) sd2 sdM0' sd1
    (fun i => ⟨hS.pre.latT (j + 1 + 1) (by omega) i, latM0' i, hS.pre.latT (j + 1) (by omega) i⟩)
  have hrep1 : Reps c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I
      (· ∈ v.tP) (v.dT j) := ⟨(hv.atT j).1, hS.rep j (by omega)⟩
  have hrep2 : Reps c.ψ (o.β (j + 1)) (o.β (j + 1 + 1)) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
      (fun i => phiOne (o.Q (j + 1) i) (o.Q (j + 1 + 1) i)) o.I (· ∈ v.tP) (v.dT (j + 1)) :=
    ⟨(hv.atT (j + 1)).1, hS.rep (j + 1) (by omega)⟩
  have hX1 := hext1.2.1 _ _ hrep1
  have hX2 := hext2.2.2 _ _ hrep2
  obtain ⟨op0, hop0, hC⟩ := GlobalTheory.T.contractionOfVacuumCombinations_proof D k ι o.p o.I _ hPl (Fin (c.X j).rank) (Fin (c.X (j + 1 + 1)).rank) c.ψ hstd
    (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (o.β j)
    (o.β₀ j (σ + 1) h) (o.β (j + 1 + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) M0 (c.x (j + 1)).L M0'
    (fun i => (o.Q j i).lat) (fun i => (o.Q (j + 1 + 1) i).lat) sdM0 sd1 sdM0'
    (fun i => ⟨(hS.glued j (σ + 1) h i).sum, (hS.glued (j + 1 + 1) σ (idx_step h) i).sum, latM0 i, latM0' i⟩) e1' e2' he1' he2'
  have hInv := (GlobalTheory.T.biVacuumOperator_zero_or_left_invertible D k ι o.p o.I _ hPl c.ψ hstd _ _ _ op0 hop0).1 (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L
    sd0 sd1 sd2
  obtain ⟨ε, -, hV⟩ := GlobalTheory.T.doubleStepSmallPairsValueAllGluedSplitPlaces_proof D k ι o.p o.I _ hPl o.q c.ψ o.χ o.hχ (fun i => (hS.pre.char i).1)
  obtain ⟨r, e, hr, hVE⟩ := hV (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) (Fin (c.X (j + 1 + 1)).rank)

  let a : PairDat o.p (c.B j (σ + 1) h).A (c.B j (σ + 1) h).V₀ (Fin (c.X j).rank) := ⟨o.β j, o.β₀ j (σ + 1) h, o.Q j⟩
  let b : MidDat o.p (c.J j (σ + 1) h).W₀ (Fin (c.X (j + 1)).rank) := ⟨o.β (j + 1), o.Q (j + 1)⟩
  let a' : PairDat o.p (c.B (j + 1 + 1) σ (idx_step h)).A (c.B (j + 1 + 1) σ (idx_step h)).V₀ (Fin (c.X (j + 1 + 1)).rank) :=
    ⟨o.β (j + 1 + 1), o.β₀ (j + 1 + 1) σ (idx_step h), o.Q (j + 1 + 1)⟩
  have hcore : ∀ i, GluedCore (c.B j (σ + 1) h) (o.M j (σ + 1) h) o.q (a.α i) (a.α₀ i) (a.P i) ∧
      GluedCore (c.B (j + 1 + 1) σ (idx_step h)) (o.M (j + 1 + 1) σ (idx_step h)) o.q (a'.α i) (a'.α₀ i) (a'.P i) ∧
      (b.β i).IsLat (c.x (j + 1)).L (b.Q i).lat := fun i =>
    ⟨hS.glued j (σ + 1) h i, hS.glued (j + 1 + 1) σ (idx_step h) i, hS.pre.latT (j + 1) (by omega) i⟩
  have hOrth : ∀ x, x ∈ v.tP → (∃ LL, OrthAt (c.B j (σ + 1) h).o M0 (c.x j).L LL x) ∧
      ∃ LL, OrthAt (c.B (j + 1 + 1) σ (idx_step h)).o M0' (c.x (j + 1 + 1)).L LL x := fun x hx => ⟨hext1.1 x hx, hext2.1 x hx⟩

  have key : ∀ t : Tup c, ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ →
      Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ →
      ∃ f₁ f₂, Vac c.ψ _ _ (o.M j (σ + 1) h) (c.x (j + 1)).L (· ∈ v.tP) (flatBF (t.sBF j (σ + 1) h) Ψ₁) ∧
        Vac c.ψ _ _ (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h)) (· ∈ v.tP) (flatFB (t.sFB j σ h) Ψ₂) ∧
        Vac c.ψ _ _ M0 (c.x (j + 1)).L (· ∈ v.tP) f₁ ∧ Vac c.ψ _ _ (c.x (j + 1)).L M0' (· ∈ v.tP) f₂ ∧
        c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ = op0.app c.ψ (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) f₁ f₂) ∧
        BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP)
          (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) f₁ f₂) ∧
        OverAll c.ψ a.α₀ b.β (o.M j (σ + 1) h) (c.x (j + 1)).L
          (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) o.I
          (flatBF (t.sBF j (σ + 1) h) Ψ₁) (comb c.ψ _ _ (extS (c.bes j (σ + 1) h).o (c.X (j + 1)) (v.dT j)) f₁) ∧
        OverAll c.ψ b.β a'.α₀ (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h))
          (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) o.I
          (flatFB (t.sFB j σ h) Ψ₂) (comb c.ψ _ _ (extT (c.bes (j + 1 + 1) σ (idx_step h)).o (c.X (j + 1)) (v.dT (j + 1))) f₂) := by
    intro t Ψ₁ Ψ₂ hΨ₁ hΨ₂
    have hF := GlobalTheory.T.flatMapPreservesVacuum_proof D c.ψ (· ∈ v.tP)
    have hXi1 := hF.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) (v.N j) (o.M j (σ + 1) h) (v.N (j + 1))
      (c.x (j + 1)).L (fun x _ => (hS.good x).bf j (σ + 1) h) Ψ₁ hΨ₁
    have hXi2 := hF.2.1 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) (v.N (j + 1)) (c.x (j + 1)).L
      (v.N (j + 1 + 1)) (o.M (j + 1 + 1) σ (idx_step h)) (fun x _ => (hS.good x).fb j σ h) Ψ₂ hΨ₂
    obtain ⟨hf1, hinv1, hov1⟩ := hR1 _ hXi1
    obtain ⟨hf2, hinv2, hov2⟩ := hR2 _ hXi2
    refine ⟨_, _, hXi1, hXi2, hf1, hf2, ?_, ?_, ?_, ?_⟩
    · have := hC _ _ hf1 hf2
      rw [hinv1, hinv2] at this
      exact this
    · exact (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hstd (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
        (c.vL j σ h) _ _ hf1.1 hf2.1).2.2 (· ∈ v.tP) (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L M0 M0' sd0 sd1 sd2 sdM0 sdM0'
        hOrth hf1 hf2
    · exact (hov1 _ _).2 (hX1.2 _ hf1)
    · exact (hov2 _ _).2 (hX2.2 _ hf2)

  have hCL : ContrLaw D := GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D
  have hCC := GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hstd (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
    (c.vL j σ h)
  rcases hInv with hz | ⟨op', hop', hinv⟩
  ·
    have happ : ∀ C, BiOp.app c.ψ (⟨0, Fin.elim0, Fin.elim0⟩ : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) C = fun _ _ => 0 :=
      fun C => by funext u w; simp [BiOp.app]
    refine ⟨ε, ⟨0, Fin.elim0, Fin.elim0⟩, r, e, hr, fun i => i.elim0, ?_⟩
    intro t _ _ _ Ψ₁ Ψ₂ hΨ₁ hΨ₂
    obtain ⟨f₁, f₂, -, -, -, -, hctr, hC0, -, -⟩ := key t Ψ₁ Ψ₂ hΨ₁ hΨ₂
    have h0 : c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ = fun _ _ => 0 := by rw [hctr, hz _ hC0]; rfl
    refine ⟨by rw [happ]; exact biVacAt_zero _ _ _ _ _, fun d d' _ _ φ _ => ?_⟩
    rw [h0, happ, biComb_zero, biComb_zero, biComb_zero]
    simp only [Comm.bl, biLift_zero, smul_zero]
  · refine ⟨ε, op', r, e, hr, hop', ?_⟩
    intro t _ hW hU Ψ₁ Ψ₂ hΨ₁ hΨ₂
    obtain ⟨f₁, f₂, hXi1, hXi2, hf₁, hf₂, hctr, hC0, hov1, hov2⟩ := key t Ψ₁ Ψ₂ hΨ₁ hΨ₂
    have hback : op'.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) = (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) f₁ f₂) := by
      rw [hctr]; exact hinv _ hC0
    refine ⟨by rw [hback]; exact hC0, fun d d' hd hd' φ hφ => ?_⟩
    rw [hback]
    have hD1 := combAt_extS (fun x => x ∉ v.tP) (c.bes j (σ + 1) h).o (c.X (j + 1)) hd
    have hD2 := combAt_extT (fun x => x ∉ v.tP) (c.bes (j + 1 + 1) σ (idx_step h)).o (c.X (j + 1)) hd'
    have hT1 := combAt_extS (· ∈ v.tP) (c.bes j (σ + 1) h).o (c.X (j + 1)) (hv.atT j).1
    have hT2 := combAt_extT (· ∈ v.tP) (c.bes (j + 1 + 1) σ (idx_step h)).o (c.X (j + 1)) (hv.atT (j + 1)).1
    have hAC1 := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank ⊕ Fin 1) c.ψ hstd _ _
      (o.β₀ j (σ + 1) h) (o.β (j + 1)) (o.M j (σ + 1) h) (c.x (j + 1)).L sdG sd1
      (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat))).2.2 _ hD1 _ hXi1
    have hAC2 := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I _ hPl (Fin (c.X (j + 1 + 1)).rank ⊕ Fin 1) (Fin (c.X (j + 1)).rank) c.ψ hstd _ _
      (o.β (j + 1)) (o.β₀ (j + 1 + 1) σ (idx_step h)) (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h)) sd1 sdG'
      (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat))).2.2 _ hD2 _ hXi2
    have th1' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hT1) hf₁.1
    have th2' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hT2) hf₂.1
    have thD1' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hD1) th1'
    have thD2' := GlobalTheory.AvgMid.theta_comb hstd (isFinComb_of_combAt _ hD2) th2'
    have hVx := hVE σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sBF j (σ + 1) h) (t.sFB j σ h)
      (c.lnk j σ h) (c.vL j σ h) (fun x hx => ⟨hU.bf j (σ + 1) h x hx, hU.fb j σ h x hx⟩) a b a' (o.M j (σ + 1) h)
      (c.x (j + 1)).L (o.M (j + 1 + 1) σ (idx_step h)) sdG sd1 sdG' hcore _ _ hAC1.1 hAC2.1 _ _ (hAC1.2 _ hov1)
      (hAC2.2 _ hov2) φ hφ
    have hSφ : IsContAut (c.X j) (a.sAll o.q (fun i => resChar (o.χ i) (o.hχ i) o.q) ε o.I φ) :=
      ((GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι o.p o.q o.χ o.hχ ε (Fin (c.X j).rank) _ _ a hS.pre.inj o.I).1.mapsTo hφ).1
    have e1 := (hCC _ _ hXi1.1 hXi2.1).2.1 d d'
    have e2 := bl_contr hCL v t hW h hφ.1 hAC1.1.1 hAC2.1.1
    have e4 := bl_contr hCL v t hW h hSφ thD1' thD2'
    have e5 := (hCC _ _ th1' th2').2.1 d d'
    have e6 := (hCC _ _ hf₁.1 hf₂.1).2.1 (v.dT j) (v.dT (j + 1))
    show c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (GlobalTheory.Unf.contr (B := c.B j (σ + 1) h) (B' := c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (flatBF (t.sBF j (σ + 1) h) Ψ₁) (flatFB (t.sFB j σ h) Ψ₂))) = _
    rw [← e1, e2, hVx, ← e4, e5, e6]
    rfl

end GlobalTheory.LevPrimeMid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLevelPrimeLawDoubleStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawLevelPrimeLaw_doubleStep : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) = o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)))) := by
  first | exact @GlobalTheory.LevPrimeMid.lawLevelPrime_double | exact GlobalTheory.LevPrimeMid.lawLevelPrime_double | (intros; apply GlobalTheory.LevPrimeMid.lawLevelPrime_double <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLevelPrimeLawAllTuples
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPrimeAll

variable {D : D7}


open GlobalTheory.FinPl.AllBij in
theorem ram_sOp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {A : HSp D} (α : ∀ i, Frame (p i) A n) (P : ι → Pair k n)
    (hinj : Function.Injective fun i => (p i).v) (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (i : ι)
    (φ : GA D A → ℂ) (hφ : IsContAut A φ ∧ ∀ j, RamAt (α j) (P j) φ) :
    IsContAut A (sOp (α i) (P i) q (resChar χ hχ q) ε φ) ∧ ∀ j, RamAt (α j) (P j) (sOp (α i) (P i) q (resChar χ hχ q) ε φ) := by
  obtain ⟨hbij, -, c, c', hc, -⟩ := GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n q χ hχ _ rfl ε A (α i) (P i)
  have hC := mapDomain_mem _ (gl_mem (α i)) c
  have hT : ∀ φ, sOp (α i) (P i) q (resChar χ hχ q) ε φ = act (Finsupp.mapDomain (α i).gl c) φ :=
    fun φ => (hc φ).trans (sum_rep_eq _ _ _)
  refine ⟨?_, fun j => ?_⟩
  · rw [hT]; exact isContAut_act _ hφ.1
  · rcases eq_or_ne j i with rfl | hj
    · exact hbij.mapsTo (hφ.2 j)
    · rw [hT]
      exact ramAt_act _ _ _ (fun x hx g => grpAt_comm A (fun e => hj (hinj e)) (hC x hx) (gl_mem _ g)) (hφ.2 j)

theorem ram_S {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (o : TDat c k ι) (hinj : Function.Injective fun i => (o.p i).v) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) (φ : GA D (c.X j) → ℂ)
    (hφ : φ ∈ o.Ram j) : o.S ε j φ ∈ o.Ram j := by
  unfold TDat.S
  induction o.I with
  | nil => exact hφ
  | cons i l ih => exact ram_sOp (o.β j) (o.Q j) hinj o.q (o.χ i) (o.hχ i) (ε j i) i _ ih

theorem exists_choice (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (hc : c.Is) (hv : v.Is) (hS : ShapeOff v o) (j : ℕ) :
    ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧
      OpAt (· ∈ v.tP) op ∧
      (∀ σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂,
        Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ →
        BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP)
          (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧
        ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j,
          c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) =
            o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ)
              (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1))
                (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))))) ∧
      ∀ (h : j + 2 * 0 + 2 = D.R.m), ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ Ψ₁ Ψ₂,
        Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.tP) Ψ₂ →
        BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP)
          (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ∧
        ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, ∀ f, IsContAut c.T f →
          ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ
              (biComb c.ψ _ _ _ d d' (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ =
            o.mono r e (t.sBF j 0 h).χW * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ)
              (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1))
                (op.app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)))) ((c.oT (j + 1 + 1) h).emb (h', 1)) ∂c.volT.μ := by
  by_cases h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m
  · obtain ⟨σ, h⟩ := h1
    obtain ⟨ε, op, r, e, hr, hop, H⟩ := GlobalTheory.T.seeSawLevelPrimeLaw_doubleStep D c v k ι o hc hv hS j σ h
    refine ⟨ε, op, r, e, hr, hop, fun σ' h' => ?_, fun h' => absurd h' (by omega)⟩
    obtain rfl : σ = σ' := by omega
    exact H
  · by_cases h2 : j + 2 * 0 + 2 = D.R.m
    · obtain ⟨ε, op, r, e, hr, hop, H⟩ := GlobalTheory.T.levelPrime_law_last_two_steps_all_tuples D c v k ι o hc hv hS j h2
      exact ⟨ε, op, r, e, hr, hop, fun σ h => absurd ⟨σ, h⟩ h1, fun _ => H⟩
    · exact ⟨fun _ => 1, ⟨0, Fin.elim0, Fin.elim0⟩, fun _ => 1, fun _ => 0, fun _ => one_pos, fun i => i.elim0,
        fun σ h => absurd ⟨σ, h⟩ h1, fun h => absurd h h2⟩

theorem lawLevelPrime_all : ∀ D : D7, GlobalTheory.SeeSaw.TOfShape D := by
  intro D c v k _ _ _ _ ι o hc hv hS
  choose ε op r e hr hop Hm Hl using exists_choice c v k ι o hc hv hS
  refine ⟨ε, op, r, e, hr, ?_, fun t w ht hW hU hK hT => ⟨?_, ?_⟩⟩
  · refine ⟨hv.disj, hv.sd, hv.sdT, hv.b, hv.bT, hv.Ψ, hv.ΨT, hv.JG, hv.atG, fun j => ⟨(hv.atT j).1, hop j⟩, fun j φ hφ => ?_⟩
    refine ⟨(hv.ram j φ hφ).1, ?_⟩
    change o.S ε j φ ∈ v.RamAd j
    change φ ∈ v.RamAd j at hφ
    rw [hS.ram j] at hφ ⊢
    exact ram_S o hS.pre.inj ε j φ hφ
  · intro j σ h Ψ₁ Ψ₂ h₁ h₂
    obtain ⟨H1, H2⟩ := Hm j σ h t ht hW hU Ψ₁ Ψ₂ h₁ h₂
    refine ⟨H1, fun d d' hd hd' φ hφ => ?_⟩
    rw [hT j (σ + 1) h]
    exact H2 d d' hd hd' φ (hS.ram j ▸ hφ)
  · intro j h Ψ₁ Ψ₂ h₁ h₂
    obtain ⟨H1, H2⟩ := Hl j h t ht hW hU hK Ψ₁ Ψ₂ h₁ h₂
    refine ⟨H1, fun d d' hd hd' φ hφ f hf _ => ?_⟩
    rw [hT j 0 h]
    exact H2 d d' hd hd' φ (hS.ram j ▸ hφ) f hf

end GlobalTheory.LevPrimeAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLevelPrimeLawAllTuplesStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_levelPrime_law_all_tuples : ∀ D : D7, GlobalTheory.SeeSaw.TOfShape D := by
  first | exact @GlobalTheory.LevPrimeAll.lawLevelPrime_all | exact GlobalTheory.LevPrimeAll.lawLevelPrime_all | (intros; apply GlobalTheory.LevPrimeAll.lawLevelPrime_all <;> assumption)
end
