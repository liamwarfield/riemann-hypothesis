module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmooth
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Smooth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

theorem isSmoothChar_fibChar {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) :
    IsSmoothChar (fibChar (k := k) a c d μ) := by
  have hA : ∀ s : ℂ, IsSmoothChar (absPow k s) := fun s => isSmoothChar_of_isUnram (isUnram_absPow k s)
  refine IsSmoothChar.mul (IsSmoothChar.mul ?_ ?_) ?_
  · exact (IsSmoothChar.detChar (hμ.inv.mul (hA _))).comp _ continuous_fst
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_fst.comp continuous_snd)
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_snd.comp continuous_snd)

private theorem isSmooth_sbRep_of_continuous_action {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (r : X → Γ → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ (x : X) (g h : Γ), r x (g * h) = r (r x g) h)
    (hc : ∀ g, Continuous fun x => r x g) (hj : Continuous fun p : X × Γ => r p.1 p.2) :
    IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep r h1 hm hc) := by
  apply GlobalTheory.SmGL.isSmooth_of_nhds
  intro φ
  obtain ⟨hlc, hcs⟩ := φ.2
  have hopen : IsOpen {z : Γ × X | (φ : X → ℂ) (r z.2 z.1) = (φ : X → ℂ) z.2} := by
    have h1lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) (r z.2 z.1)) :=
      hlc.comp_continuous (hj.comp continuous_swap)
    have h2lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) z.2) :=
      hlc.comp_continuous continuous_snd
    have := (h1lc.comp₂ h2lc (fun u v => u - v)).isOpen_fiber 0
    simpa only [sub_eq_zero] using this
  have hev : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ), (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x := by
    refine IsCompact.eventually_forall_of_forall_eventually hcs ?_
    intro x _
    exact hopen.mem_nhds (by simp only [Set.mem_ofPred_eq, h1])
  have hev' : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ),
      (φ : X → ℂ) (r x γ⁻¹) = (φ : X → ℂ) x := by
    have ht : Filter.Tendsto (fun γ : Γ => γ⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : Γ))
    exact ht.eventually hev
  filter_upwards [hev, hev'] with γ hγ hγ'
  apply Subtype.ext
  funext x
  show (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x
  by_cases hx : x ∈ tsupport (φ : X → ℂ)
  · exact hγ x hx
  · by_cases hy : r x γ ∈ tsupport (φ : X → ℂ)
    · have e := hγ' _ hy
      rw [← hm, mul_inv_cancel, h1] at e
      exact e.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

private theorem isSmooth_fibBase (κ : ℕ) : IsSmooth (fibBase (k := k) a c κ) := by
  show IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep _ _ _ _)
  apply isSmooth_sbRep_of_continuous_action
  apply Continuous.subtype_mk
  have hinv : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (((p.2.2)⁻¹ : GL c k) : Matrix c c k) :=
    Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_snd))
  have hx : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (p.1 : Matrix c a k) :=
    continuous_subtype_val.comp continuous_fst
  have hg : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      ((p.2.1 : GL a k) : Matrix a a k) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  exact (hinv.matrix_mul hx).matrix_mul hg

theorem isSmooth_fibRep_levi (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) (κ : ℕ) :
    IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  have hB := isSmooth_fibBase (k := k) a c κ
  have hρ := isSmooth_comp hB ((MonoidHom.id (GL a k)).prodMap (MonoidHom.fst (GL c k) (GL d k)))
    (continuous_id.prodMap continuous_fst)
  have ht := isSmooth_twist hρ (isSmoothChar_fibChar a c d hμ)
  exact isSmooth_comp ht (MonoidHom.inr (GL a k) (GL c k × GL d k)) (continuous_const.prodMk continuous_id)

end Smooth

end GlobalTheory.CompanionTheory.ThetaGLLen

namespace GlobalTheory.CompanionTheory.ThetaGLLen

theorem isSmooth_fibRep_inr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  intro k _ _ _ _ a c d _ _ _ _ _ _ μ hμ κ
  exact isSmooth_fibRep_levi a c d μ hμ κ

end GlobalTheory.CompanionTheory.ThetaGLLen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmoothStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_representation_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | exact GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormCoboundaryRelation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormCoboundaryRelation
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.GrDelta
open GlobalTheory.CompanionTheory.CocProd

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem sqMap_val {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {T T' : C} (φ : T ⟶ T') (z : sqM a b T)
    (u : A.obj T) (h : z.1 = Ideal.Quotient.mk _ u) :
    (sqMap a b φ z).1 = Ideal.Quotient.mk _ ((A.map φ).hom u) := by
  obtain ⟨x, hx⟩ := z
  obtain rfl : x = _ := h
  rfl

variable {d : ℕ} (Q : Poly Φ) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T)

theorem Pmap_j_apply {T T' : C} (φ : T ⟶ T') (u : Φ.A.obj T) :
    (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom ((Φ.A.map (Q.j T)).hom u) =
      (Φ.A.map (Q.j T')).hom ((Φ.A.map φ).hom u) := by
  exact (Cut.mapA_comp _ _ u).symm.trans
    ((congrArg (fun f => (Φ.A.map f).hom u) (Cut.Pmap_j Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).trans
      (Cut.mapA_comp _ _ u))

theorem Pmap_shift {T₀ T T' : C} (ψ : T₀ ⟶ T) (φ : T ⟶ T') :
    (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom
      (Q.X T + (Φ.A.map (Q.j T)).hom (E.a σ 0 ψ)) =
      Q.X T' + (Φ.A.map (Q.j T')).hom (E.a σ 0 (ψ ≫ φ)) := by
  have h : (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom (Q.X T) =
      Q.X T' + (Φ.A.map (Q.j T')).hom (E.a σ 0 φ) :=
    Cut.Pmap_X Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ
  rw [map_add (f := _), Pmap_j_apply, a_comp, map_add (f := _), h]
  abel

def Bv {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) : Φ.A.obj (Q.P (s.obj (Fin.last n))) :=
  Q.X _ + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.le_last p))))

theorem Bv_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) :
    Bv Q E σ s p ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
  have h : Bv Q E σ s p ∈ Φ.J.S _ := Ideal.add_mem _ (Q.X_mem _) (Φ.J.map_mem _ (E.mem 0 _ _))
  rw [Nat.cast_one, hF.one]
  exact h

theorem term_val {Fil : ℤ → IdF Φ.A} {j : ℕ} {r : ℤ} (I : Fin j → Fin d) (x : Φ.A.obj E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j)
    (hy : ∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s)))
    (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (show sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1)))) from
      ((Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r).map (toLast i s)).hom (y (face i s))).1 =
      Ideal.Quotient.mk _ (Bv Q E σ s (i.succAbove 0) *
        (Φ.A.map (Q.j _)).hom ((Φ.A.map (toLast i s)).hom (E.form σ (Fin.succ ∘ I) x (face i s)))) := by
  refine (sqMap_val (Fil r) (Fil (r + 1)) (Cut.Pmap Q (X := (Pt.Sσ σ).obj _) (Y := (Pt.Sσ σ).obj _) (toLast i s))
    (y (face i s)) _ (hy (face i s))).trans ?_
  have e : (face i s).map (homOfLE (Fin.zero_le (Fin.last j))) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove 0))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  have h1 := Pmap_shift Q E σ ((face i s).map (homOfLE (Fin.zero_le (Fin.last j)))) (toLast i s)
  have h2 := Pmap_j_apply Q E σ (toLast i s) (E.form σ (Fin.succ ∘ I) x (face i s))
  rw [e] at h1
  exact congrArg (Ideal.Quotient.mk _) ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 h2))

theorem Bv_zero {n : ℕ} (s : ComposableArrows C (n + 1)) :
    Bv Q E σ s 0 = Bv Q E σ s 1 + (Φ.A.map (Q.j _)).hom (ga E σ 0 s 0 1 (Fin.zero_le _)) := by
  have e : s.map (homOfLE (Fin.le_last (0 : Fin (n + 2)))) =
      s.map (homOfLE (Fin.zero_le (1 : Fin (n + 2)))) ≫ s.map (homOfLE (Fin.le_last (1 : Fin (n + 2)))) := by
    rw [← s.map_comp]; rfl
  unfold Bv ga
  rw [e, a_comp, map_add (f := _)]
  abel

theorem form_cons {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) :
    E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s =
      ga E σ 0 s 0 1 (Fin.zero_le _) * (Φ.A.map (toLast 0 s)).hom (E.form σ (Fin.succ ∘ I) x (face 0 s)) := by
  rw [face_form]
  have hl : (0 : Fin (j + 2)).succAbove (Fin.last j) = Fin.last (j + 1) := by simp
  have hW : (Φ.A.map (toLast 0 s)).hom ((Φ.A.map (σ _)).hom x) = (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x := by
    rw [map_map, show σ _ ≫ toLast 0 s = σ (s.obj (Fin.last (j + 1))) from sec_last E σ s _ hl]
  rw [hW]
  unfold Frame.form
  rw [Fin.prod_univ_succ, mul_assoc]
  congr 2

theorem alt_sum {S S' F : Type*} [CommRing S] [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (J : F) (n : ℕ)
    (t : Fin (n + 1) → S) (b : Fin (n + 1) → S') (B : S') (g : S) (h0 : B = b 0 + J g)
    (hs : ∀ k : Fin n, b k.succ = B) :
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (b i * J (t i)) =
      B * J (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • t i) - J (g * t 0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i : Fin (n + 1) => B * J ((-1 : ℤ) ^ (i : ℕ) • t i))]
  have h : ∀ k : Fin n, (-1 : ℤ) ^ (k.succ : ℕ) • (b k.succ * J (t k.succ)) = B * J ((-1 : ℤ) ^ (k.succ : ℕ) • t k.succ) := by
    intro k
    rw [hs, map_zsmul, mul_smul_comm]
  rw [Finset.sum_congr rfl fun k _ => h k]
  simp only [Fin.val_zero, pow_zero, one_smul, map_mul, h0]
  ring

theorem gr_delta {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ)
    (hr : r = j + 1 + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j) (w : CH.Cn (gr Fil r) (j + 1))
    (hy : ∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s)))
    (hw : ∀ s, (show sqM _ _ _ from w s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) :
    CH.d _ j y = -(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w := by
  funext s
  apply Subtype.ext
  have hL : Subtype.val (CH.d _ j y s : sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) =
      Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Bv Q E σ s (i.succAbove 0) *
        (Φ.A.map (Q.j _)).hom ((Φ.A.map (toLast i s)).hom (E.form σ (Fin.succ ∘ I) x (face i s))))) := by
    change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r).map (toLast i s)).hom (y (face i s)) :
      sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    refine Eq.trans ?_ (congrArg (fun z => (-1 : ℤ) ^ (i : ℕ) • z) (term_val Q E σ I x y hy s i))
    rfl
  have hR : Subtype.val ((-(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w) s :
      sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) =
      -Ideal.Quotient.mk _ ((Φ.A.map (Q.j _)).hom (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) :=
    congrArg Neg.neg (sqMap_val (Fil r) (Fil (r + 1)) (Q.j (s.obj (Fin.last (j + 1)))) (w s) _ (hw s))
  refine hL.trans (Eq.trans ?_ hR.symm)
  change Ideal.Quotient.mk ((Fil (r + 1)).S (Q.P (s.obj (Fin.last (j + 1))))) _ =
    -Ideal.Quotient.mk ((Fil (r + 1)).S (Q.P (s.obj (Fin.last (j + 1))))) _
  rw [alt_sum (Φ.A.map (Q.j _)).hom (j + 1) _ (fun i => Bv Q E σ s (i.succAbove 0)) (Bv Q E σ s 0)
    (ga E σ 0 s 0 1 (Fin.zero_le _))
    (by simpa using Bv_zero Q E σ s) (fun k => by simp), ← map_neg, Ideal.Quotient.eq, form_cons]
  have hD := d_form_mem E σ hF hc j q (Fin.succ ∘ I) x hx s
  have hJ := (Fil (((j : ℤ) + q) + 1)).map_mem (Q.j (s.obj (Fin.last (j + 1)))) hD
  have e1 : (((j + q + 1 : ℕ) : ℤ)) = ((j : ℤ) + q) + 1 := by push_cast; ring
  rw [← e1] at hJ
  have hm := hF.mul 1 (j + q + 1) _ (Bv_mem Q E σ hF s 0) hJ
  have e2 : (((1 + (j + q + 1) : ℕ) : ℤ)) = r + 1 := by rw [hr]; push_cast; ring
  rw [e2] at hm
  convert hm using 1
  ring

end GlobalTheory.CompanionTheory.GrDelta
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormCoboundaryRelationStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_form_coboundary_relation : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ)
    (hr : r = j + 1 + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j) (w : CH.Cn (gr Fil r) (j + 1)),
    (∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s))) →
    (∀ s, (show sqM _ _ _ from w s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) →
    CH.d _ j y = -(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w := by
  first | exact @GlobalTheory.CompanionTheory.GrDelta.gr_delta | exact GlobalTheory.CompanionTheory.GrDelta.gr_delta | (intros; apply GlobalTheory.CompanionTheory.GrDelta.gr_delta <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrame
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LocGr

theorem H_succ_subsingleton {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {T₀ : C}
    (h : Limits.IsInitial T₀) (n : ℕ) : Subsingleton (CH.H F (n + 1)) := by
  have key : ∀ c : CH.H F (n + 1), c = 0 := by
    intro c
    obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨g, hg⟩ := (CrystallineSemistableComparison.P.initial F T₀ h).2.2.2 n f hf
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change f ∈ (CH.cx F).B (n + 1)
    exact ⟨g, hg.trans (one_smul R f)⟩
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem H_zero_subsingleton {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {r : ℤ} (hr : r < 0) : Subsingleton (CH.H (gr Fil r) 0) := by
  have hT : ∀ T, Subsingleton ((gr Fil r).obj T) := fun T => by
    have h1 : (Fil (r + 1)).S T = ⊤ := hF.top _ (by omega) T
    have h2 : Subsingleton (Φ.A.obj T ⧸ (Fil (r + 1)).S T) := Ideal.Quotient.subsingleton_iff.2 h1
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim (α := Φ.A.obj T ⧸ (Fil (r + 1)).S T) _ _)⟩
  have hC : Subsingleton (CH.Cn (gr Fil r) 0) := ⟨fun a b => funext fun s => (hT _).elim _ _⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have e : f = g := hC.elim f g
  subst e
  rfl

theorem gr_zero : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (E : Frame Φ 0) (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (j : ℕ),
    (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D := by
  intro R _ C _ Φ Fil hF E σ r j
  have hI : Limits.IsInitial E.D := E.initial
  refine ⟨fun hr => ?_, fun q hq => ?_⟩
  · cases j with
    | zero => exact H_zero_subsingleton hF (by simpa using hr)
    | succ n => exact H_succ_subsingleton _ hI n
  · cases j with
    | succ n =>
      have hs := H_succ_subsingleton (gr Fil r) hI n
      haveI : IsEmpty (Idx (n + 1) 0) := ⟨fun I => (I.1 0).elim0⟩
      refine ⟨fun c => ⟨fun I => isEmptyElim I, fun I => isEmptyElim I, ?_⟩, fun x _ _ I => isEmptyElim I⟩
      unfold CrystallineSemistableComparison.Pb.Rep
      refine ⟨0, map_zero _, Subsingleton.elim _ _, fun s => ?_⟩
      have e := Fintype.sum_empty (fun I : Idx (n + 1) 0 => E.form σ I.1 (isEmptyElim I) s)
      refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) e).symm
      exact (map_zero _).symm
    | zero =>
      have hq' : r = q := by simpa using hq
      subst hq'
      haveI : Unique (Idx 0 0) := ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩⟩, fun I => Subtype.ext (funext fun a => a.elim0)⟩
      have hform : ∀ (x : Idx 0 0 → Φ.A.obj E.D) (s : ComposableArrows C 0),
          ∑ I : Idx 0 0, E.form σ I.1 (x I) s = (Φ.A.map (σ _)).hom (x default) := by
        intro x s
        rw [Fintype.sum_unique]
        simp [Frame.form]
      refine ⟨fun c => ?_, fun x hx hrep I => ?_⟩
      · obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨m, hm⟩ := (CrystallineSemistableComparison.P.initial (gr Fil (q : ℤ)) E.D hI).2.2.1 f hf
        obtain ⟨m', hm'⟩ := m
        obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hm'
        refine ⟨fun _ => y, fun _ => hy, ?_⟩
        unfold CrystallineSemistableComparison.Pb.Rep
        refine ⟨f, hf, rfl, fun s => ?_⟩
        refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) (hform (fun _ => y) s)).symm
        have h1 := congrFun (hm.trans (one_smul R f)) s
        have h2 := congrArg Subtype.val h1
        rw [show σ (s.obj (Fin.last 0)) = hI.to _ from hI.hom_ext _ _]
        exact h2.symm
      · unfold CrystallineSemistableComparison.Pb.Rep at hrep
        obtain ⟨f, hf, h0, hs⟩ := hrep
        have hf0 : f = 0 := by
          have h3 : (⟨f, hf⟩ : (CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) ∈
              ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).B 0).submoduleOf ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) :=
            (Submodule.Quotient.mk_eq_zero _).1 h0.symm
          exact (Submodule.mem_bot R).1 h3
        subst hf0
        have h1 := (hs (ComposableArrows.mk₀ E.D)).trans (congrArg (Ideal.Quotient.mk _) (hform x _))
        have hσ : σ ((ComposableArrows.mk₀ E.D).obj (Fin.last 0)) = 𝟙 E.D := hI.hom_ext _ _
        rw [hσ] at h1
        have h4 : (Φ.A.map (𝟙 E.D)).hom (x default) = x default := by
          rw [Φ.A.map_id]; rfl
        have h5 : Ideal.Quotient.mk ((Fil ((q : ℤ) + 1)).S E.D) (x default) = 0 := by
          rw [← h4]
          exact h1.symm
        rw [Subsingleton.elim I default]
        exact Ideal.Quotient.eq_zero_iff_mem.1 h5

end GlobalTheory.CompanionTheory.LocGr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrameStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_cohomology_of_frame : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (E : CrystallineSemistableComparison.Pb.Frame Φ 0)
    (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (j : ℕ),
    (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D := by
  intro R _ C _ Φ Fil hF E σ r j
  have hI : Limits.IsInitial E.D := Limits.IsInitial.ofUniqueHom σ fun _ f =>
    (E.bij f (fun _ => 0) (fun _ => Ideal.zero_mem _)).unique
      (fun i => i.elim0) (fun i => i.elim0)
  have hSucc (n : ℕ) : Subsingleton (CH.H (gr Fil r) (n + 1)) :=
    GlobalTheory.CompanionTheory.LocGr.H_succ_subsingleton _ hI n
  refine ⟨fun hr => ?_, fun q hq => ?_⟩
  · cases j with
    | zero =>
      exact GlobalTheory.CompanionTheory.LocGr.H_zero_subsingleton hF (by simpa using hr)
    | succ n => exact hSucc n
  · cases j with
    | succ n =>
      have : Subsingleton (CH.H (gr Fil r) (n + 1)) := hSucc n
      have : IsEmpty (Idx (n + 1) 0) := ⟨fun I => (I.1 0).elim0⟩
      refine ⟨fun c => ⟨fun I => isEmptyElim I, fun I => isEmptyElim I, ?_⟩,
        fun _ _ _ I => isEmptyElim I⟩
      unfold CrystallineSemistableComparison.Pb.Rep
      refine ⟨0, map_zero _, Subsingleton.elim _ _, fun s => ?_⟩
      have e := Fintype.sum_empty (fun I : Idx (n + 1) 0 => E.form σ I.1 (isEmptyElim I) s)
      refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) e).symm
      exact (map_zero _).symm
    | zero =>
      have hq' : r = q := by simpa using hq
      subst hq'
      have : Unique (Idx 0 0) :=
        ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩⟩, fun I => Subtype.ext (funext fun a => a.elim0)⟩
      have hform (x : Idx 0 0 → Φ.A.obj E.D) (s : ComposableArrows C 0) :
          ∑ I : Idx 0 0, E.form σ I.1 (x I) s = (Φ.A.map (σ _)).hom (x default) := by
        rw [Fintype.sum_unique]
        simp [CrystallineSemistableComparison.Pb.Frame.form]
      refine ⟨fun c => ?_, fun x _ hrep I => ?_⟩
      · obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨m, hm⟩ :=
          (CrystallineSemistableComparison.P.initial (gr Fil (q : ℤ)) E.D hI).2.2.1 f hf
        obtain ⟨m', hm'⟩ := m
        obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hm'
        refine ⟨fun _ => y, fun _ => hy, ?_⟩
        unfold CrystallineSemistableComparison.Pb.Rep
        refine ⟨f, hf, rfl, fun s => ?_⟩
        refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) (hform (fun _ => y) s)).symm
        have h1 := congrFun (hm.trans (one_smul R f)) s
        have h2 := congrArg Subtype.val h1
        rw [show σ (s.obj (Fin.last 0)) = hI.to _ from hI.hom_ext _ _]
        exact h2.symm
      · unfold CrystallineSemistableComparison.Pb.Rep at hrep
        obtain ⟨f, hf, h0, hs⟩ := hrep
        have hf0 : f = 0 := by
          have h3 : (⟨f, hf⟩ : (CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) ∈
              ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).B 0).submoduleOf
                ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) :=
            (Submodule.Quotient.mk_eq_zero _).1 h0.symm
          exact (Submodule.mem_bot R).1 h3
        subst f
        have h1 := (hs (ComposableArrows.mk₀ E.D)).trans (congrArg (Ideal.Quotient.mk _) (hform x _))
        have hσ : σ ((ComposableArrows.mk₀ E.D).obj (Fin.last 0)) = 𝟙 E.D := hI.hom_ext _ _
        rw [hσ] at h1
        have h4 : (Φ.A.map (𝟙 E.D)).hom (x default) = x default := by
          rw [Φ.A.map_id]
          rfl
        have h5 : Ideal.Quotient.mk ((Fil ((q : ℤ) + 1)).S E.D) (x default) = 0 := by
          rw [← h4]
          exact h1.symm
        rw [Subsingleton.elim I default]
        exact Ideal.Quotient.eq_zero_iff_mem.1 h5
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibre
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibre
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

def topR (e : c ⊕ d ≃ b) (y : Matrix c a k) : Matrix b a k := (fromRows y 0).submatrix e.symm id

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
@[simp] theorem topR_inl (e : c ⊕ d ≃ b) (y : Matrix c a k) (i : c) (l : a) :
    topR e y (e (.inl i)) l = y i l := by
  simp [topR]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
@[simp] theorem topR_inr (e : c ⊕ d ≃ b) (y : Matrix c a k) (i : d) (l : a) :
    topR e y (e (.inr i)) l = 0 := by
  simp [topR]

theorem mul_topR (e : c ⊕ d ≃ b) (g : Matrix b b k) (y : Matrix c a k) (i : b) (l : a) :
    (g * topR e y) i l = ∑ m, g i (e (.inl m)) * y m l := by
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp

theorem topR_mul (e : c ⊕ d ≃ b) (y : Matrix c a k) (g : Matrix a a k) :
    topR e (y * g) = topR e y * g := by
  ext i l
  obtain ⟨i | i, rfl⟩ := e.surjective i <;> simp [Matrix.mul_apply]

theorem rank_topR (e : c ⊕ d ≃ b) (y : Matrix c a k) : (topR e y).rank = y.rank := by
  refine le_antisymm ?_ ?_
  · have h : topR e y = ((1 : Matrix b b k).submatrix id fun i => e (.inl i)) * y := by
      ext i l
      obtain ⟨i | i, rfl⟩ := e.surjective i
      · rw [topR_inl, Matrix.mul_apply]
        change y i l = ∑ j, (1 : Matrix b b k) (e (.inl i)) (e (.inl j)) * y j l
        simp [Matrix.one_apply, e.injective.eq_iff]
      · simp [Matrix.mul_apply, one_apply]
    rw [h]
    exact rank_mul_le_right _ _
  · have h : (topR e y).submatrix (fun i => e (.inl i)) (Equiv.refl a) = y := by
      ext i l; simp
    have h2 := rank_submatrix_le (topR e y) (fun i => e (.inl i)) (Equiv.refl a)
    rwa [h] at h2

def topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} (y : RankIn (k := k) (a := a) (b := c) {κ}) :
    RankIn (k := k) (a := a) (b := b) {κ} :=
  ⟨topR e y.1, (rank_topR e y.1).trans y.2⟩

theorem range_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} :
    Set.range (topEmbR (k := k) (a := a) e (κ := κ)) = {x | ∀ j i, x.1 (e (.inr j)) i = 0} := by
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩ j i
    exact topR_inr e _ j i
  · have hxy : x.1 = topR e (x.1.submatrix (fun i => e (.inl i)) id) := by
      ext i l
      obtain ⟨i | i, rfl⟩ := e.surjective i
      · simp
      · simpa using hx i l
    have hr : (x.1.submatrix (fun i => e (.inl i)) id).rank = κ := by
      rw [← rank_topR e, ← hxy]
      exact x.2
    exact ⟨⟨_, hr⟩, Subtype.ext hxy.symm⟩

theorem isClosedEmbedding_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} :
    IsClosedEmbedding (topEmbR (k := k) (a := a) e (κ := κ)) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨IsEmbedding.of_comp (g := fun x : RankIn (k := k) (a := a) (b := b) {κ} =>
    x.1.submatrix (fun i => e (.inl i)) id)
    (Continuous.subtype_mk (continuous_matrix fun i l => ?_) _)
    (continuous_subtype_val.matrix_submatrix _ _) ?_, ?_⟩
  · obtain ⟨i | i, rfl⟩ := e.surjective i
    · simp only [topR_inl]
      exact continuous_subtype_val.matrix_elem _ _
    · simp only [topR_inr]
      exact continuous_const
  · convert IsEmbedding.subtypeVal (p := fun y : Matrix c a k => y.rank ∈ ({κ} : Set ℕ)) using 1
    funext y
    ext i l
    exact topR_inl e _ i l
  · rw [range_topEmbR]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_subtype_val.matrix_elem _ _) continuous_const

theorem lAct_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ}
    (y : RankIn (k := k) (a := a) (b := c) {κ}) (p : parab k (two e)) :
    lAct _ (topEmbR e y) p = topEmbR e (lAct _ y (show GL c k from leviProj k (two e) p false)) := by
  refine Subtype.ext ?_
  rw [lAct_val]
  ext i l
  refine (mul_topR e _ _ i l).trans ?_
  obtain ⟨i | i, rfl⟩ := e.surjective i
  · refine Eq.trans ?_ (topR_inl e _ i l).symm
    rw [lAct_val]
    have : (show GL c k from leviProj k (two e) p false)⁻¹ = leviProj k (two e) p⁻¹ false := by
      rw [map_inv]; rfl
    rw [this]
    rfl
  · refine Eq.trans ?_ (topR_inr e _ i l).symm
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [(mem_parab_two k).1 (inv_mem p.2), zero_mul]

theorem eq_zero_of_vecMul (e : c ⊕ d ≃ b) {κ : ℕ} (hκ : κ = Fintype.card c)
    (y : RankIn (k := k) (a := a) (b := c) {κ})
    (v : c → k) (h : v ᵥ* y.1 = 0) : v = 0 := by
  refine GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k a c d b e (topR e y.1)ᵀ
    ((rank_transpose _).trans (((rank_topR e y.1).trans y.2).trans hκ)) (fun i j => topR_inr e _ j i) v ?_
  have hs : (topR e y.1)ᵀ.submatrix id (fun i => e (.inl i)) = y.1ᵀ := by
    ext i l; simp
  rw [hs, mulVec_transpose, h]

theorem exists_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} (hκ : κ = Fintype.card c)
    (x : RankIn (k := k) (a := a) (b := b) {κ}) :
    ∃ y, ∃ w ∈ KO k b, x = lAct _ (topEmbR e y) w := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k a c d b e x.1ᵀ ((rank_transpose _).trans (x.2.trans hκ))
  obtain ⟨u, hu⟩ := (isUnit_transpose _).2 g.isUnit
  obtain ⟨p, hp, w, hw, h⟩ := iwasawa_blockTriangular k b (fun i => (blk (two e) i).toNat) u
  have hp' : p ∈ parab k (two e) := (mem_parab_two k).2 fun i j => hp (by
    rw [← two_false e, ← two_true e]; simp only [blk_apply]; simp)
  have : lAct _ x u⁻¹ ∈ Set.range (topEmbR (k := k) (a := a) e (κ := κ)) := by
    rw [range_topEmbR]
    intro j i
    rw [lAct_val, inv_inv, hu, ← transpose_transpose x.1, ← transpose_mul]
    exact hg i j
  obtain ⟨y, hy⟩ := this
  refine ⟨_, w, hw, Eq.trans ?_ (congrArg (lAct _ · w) (lAct_topEmbR e y ⟨p, hp'⟩))⟩
  show x = lAct _ (lAct _ _ p) w
  rw [hy, ← lAct_mul, ← lAct_mul, ← h, inv_mul_cancel, lAct_one]

theorem fibChar_fst (e : c ⊕ d ≃ b) (μ : kˣ →* ℂˣ) (γ : GL a k) :
    fibChar a c d μ (γ, 1, 1) = omChar a b μ (γ, 1) := by
  have hb : ((Fintype.card c : ℂ) + Fintype.card d) / 2 = (Fintype.card b : ℂ) / 2 := by
    rw [← Fintype.card_congr e, Fintype.card_sum]; push_cast; ring
  simp [fibChar, omChar, hb]

theorem fibStr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b c d : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (κ : ℕ), κ = Fintype.card c → ∀ μ : kˣ →* ℂˣ,
    IsSmoothChar μ → Nonempty ((omegaOn a b μ {κ}).Equiv (indSnd e (fibRep a c d μ κ))) := by
  intro k _ _ _ _ a b c d _ _ _ _ _ _ _ _ e κ hκ μ hμ
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨E, hE⟩ := GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced (GL b k)
    (RankIn (k := k) (a := a) (b := b) {κ}) (RankIn (k := k) (a := a) (b := c) {κ})
    (SB (RankIn (k := k) (a := a) (b := c) {κ})) (lAct {κ}) (lAct_one _) (lAct_mul _) (continuous_lAct _)
    (topEmbR e) (isClosedEmbedding_topEmbR e) (parab k (two e)) (KO k b) SplitFlip.isCompact_KO
    (exists_topEmbR e hκ)
    (fun y p => lAct _ y (show GL c k from leviProj k (two e) p false)) (lAct_topEmbR e)
    (fun y y' g h => by
      refine inv_mem_iff.1 ((mem_parab_two k).2 fun j i => ?_)
      have h0 : (fun m => (g⁻¹).val (e (.inr j)) (e (.inl m))) ᵥ* y.1 = 0 := by
        funext l
        have := congrArg (fun x : RankIn (k := k) (a := a) (b := b) {κ} => x.1 (e (.inr j)) l) h
        simp only [lAct_val] at this
        exact (mul_topR e _ _ _ l).symm.trans (this.trans (topR_inr e _ j l))
      exact congrFun (eq_zero_of_vecMul e hκ y _ h0) i)
    ((omChar a b μ).comp (MonoidHom.inr _ _))
    ((isSmoothChar_omChar hμ).comp _ (continuous_const.prodMk continuous_id))
    ((twist (MonoidHom.comp ((fibRep a c d μ κ).comp (MonoidHom.inr _ _)) (leviTwo k c d).symm.toMonoidHom)
      (deltaHalf k (Two c d))).comp (leviProj k (two e)))
    (LinearEquiv.refl ℂ _)
    (fun p w y => by
      set m := leviProj k (two e) p with hm
      have hd : GeneralLinearGroup.det (p : GL b k) =
          GeneralLinearGroup.det (m false) * GeneralLinearGroup.det (m true) :=
        (det_parab k (two e) p).trans ((Fintype.prod_bool _).trans (mul_comm _ _))
      have hδ := deltaHalf_two (k := k) (m false, m true)
      rw [show leviTwo k c d (m false, m true) = m from (leviTwo k c d).right_inv m] at hδ
      show (deltaHalf k (Two c d) m : ℂ) * (fibRep a c d μ κ (1, m false, m true) w).1 y = _
      rw [fibRep_apply, ← mul_assoc, ← Units.val_mul]
      refine congrArg₂ _ (congrArg _ ?_) rfl
      rw [hδ]
      simp only [fibChar, omChar, MonoidHom.comp_apply, MonoidHom.mul_apply, detChar_apply,
        MonoidHom.inr_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, one_mul, hd, map_mul,
        neg_div, absPow_neg, MonoidHom.inv_apply, absPow_add, mul_inv, inv_inv, inv_one]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp)
  have hE' : ∀ Φ g y, ((E Φ).1.1 g).1 y =
      (omChar a b μ (1, g) : ℂ) * Φ.1 (lAct _ (topEmbR e y) g) := hE
  refine ⟨.mk E fun g => LinearMap.ext fun Φ => Subtype.ext (Subtype.ext (funext fun x =>
    Subtype.ext (funext fun y => ?_)))⟩
  obtain ⟨γ, h⟩ := g
  refine (hE' _ x y).trans (Eq.trans ?_ (fibRep_apply a c d μ κ γ 1 1 ((E Φ).1.1 (x * h)) y).symm)
  rw [hE', omegaOn_apply, fibChar_fst e, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul,
    ← map_mul, ← map_mul]
  refine congrArg₂ _ (congrArg _ (congrArg _ (by simp))) (congrArg _ (Subtype.ext ?_))
  simp only [lAct_val, act, topEmbR, Units.val_mul, topR_mul, _root_.mul_inv_rev, Matrix.mul_assoc,
    Units.val_one, Matrix.one_mul, inv_one, Matrix.mul_one]

end GlobalTheory.CompanionTheory.ThetaGLLen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibreStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_equiv_induced_fibre : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b c d : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (κ : ℕ), κ = Fintype.card c → ∀ μ : kˣ →* ℂˣ, IsSmoothChar μ → Nonempty ((omegaOn a b μ {κ}).Equiv (indSnd e (fibRep a c d μ κ))) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.fibStr | exact GlobalTheory.CompanionTheory.ThetaGLLen.fibStr | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.fibStr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem homIdeal_homog {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) :
    ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  intro f hf n
  have hI : (homIdeal i).IsHomogeneous (grK K N) := by
    refine Ideal.homogeneous_span (grK K N) _ ?_
    rintro g ⟨d, hg, -⟩
    exact ⟨d • 1, hg⟩
  have h := hI n hf
  have e : ((DirectSum.decompose (grK K N) f n : grK K N n) : MvPolynomial (Fin (N + 1)) K) =
      MvPolynomial.homogeneousComponent n f :=
    MvPolynomial.decomposition.decompose'_apply f n
  exact e ▸ h

end GlobalTheory.CompanionTheory.Geo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMemStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_component_mem : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  first | exact @GlobalTheory.CompanionTheory.Geo.homIdeal_homog | exact GlobalTheory.CompanionTheory.Geo.homIdeal_homog | (intros; apply GlobalTheory.CompanionTheory.Geo.homIdeal_homog <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GalDual

theorem contAction_twDual_of_continuous {R Γ M : Type*} [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [AddCommGroup M]
    [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (χ : Γ →* Rˣ)
    (hχ : Continuous χ) (ρ : Representation R Γ M) (hρ : ContAction ρ) :
    ContAction (twDual χ ρ) := by
  have key : ∀ φ : TDual R M, Continuous (fun g : Γ => twDual χ ρ g φ) := by
    intro φ
    rw [continuous_discrete_rng]
    intro ψ
    have hset : (fun g : Γ => twDual χ ρ g φ) ⁻¹' {ψ} =
        ⋂ m : M, (fun g : Γ => ((χ g : Rˣ) : R) * φ (ρ g⁻¹ m)) ⁻¹' {ψ m} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      exact ⟨fun h m => by rw [← h]; rfl, fun h => DFunLike.ext _ _ h⟩
    rw [hset]
    refine isOpen_iInter_of_finite fun m => ?_
    have h1 : Continuous fun g : Γ => ρ g⁻¹ m :=
      Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) hρ
        (continuous_inv.prodMk continuous_const)
    have h2 : Continuous fun g : Γ => φ (ρ g⁻¹ m) :=
      (continuous_of_discreteTopology (f := fun x : M => φ x)).comp h1
    have h3 : Continuous fun g : Γ => ((χ g : Rˣ) : R) * φ (ρ g⁻¹ m) :=
      (Units.continuous_val.comp hχ).mul h2
    exact (isOpen_discrete {ψ m}).preimage h3
  exact continuous_prod_of_discrete_right.2 key

theorem contAction_twDual : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ), μ.comp (toGS Ω _) = cycMod F Ω l r → ContAction (twDual μ ρ) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hμ
  have hc : Continuous μ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (μ ∘ QuotientGroup.mk : G F Ω → _) = cycMod F Ω l r := by rw [← hμ]; rfl
    rw [this]; exact continuous_cycMod
  exact contAction_twDual_of_continuous μ hc ρ hρ

end GlobalTheory.CompanionTheory.GalDual
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExactStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmer_group_dual_exact : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), μ.comp (toGS Ω _) = cycMod F Ω l r → ContAction (twDual μ ρ) := by
  first | exact @GlobalTheory.CompanionTheory.GalDual.contAction_twDual | exact GlobalTheory.CompanionTheory.GalDual.contAction_twDual | (intros; apply GlobalTheory.CompanionTheory.GalDual.contAction_twDual <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRespectsFiltration
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRespectsFiltration
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FormMem

theorem prod_fil_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (T : C) : ∀ (n : ℕ) (f : Fin n → Φ.A.obj T), (∀ k, f k ∈ (Fil 1).S T) →
      ∏ k, f k ∈ (Fil (n : ℤ)).S T := by
  intro n
  induction n with
  | zero =>
    intro f _
    rw [hF.top ((0 : ℕ) : ℤ) (by simp) T]
    exact Submodule.mem_top
  | succ n ih =>
    intro f h
    rw [Fin.prod_univ_succ]
    simpa only [Nat.add_comm 1 n] using
      hF.mul 1 n T (h 0) (ih (fun k => f k.succ) fun k => h k.succ)

theorem form_mem : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  refine hF.mul j q _ (prod_fil_mem hF _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _

end GlobalTheory.CompanionTheory.FormMem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRespectsFiltrationStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_form_respects_filtration : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  have prod_fil_mem (T : C) (n : ℕ) (f : Fin n → Φ.A.obj T)
      (hf : ∀ k, f k ∈ (Fil 1).S T) : ∏ k, f k ∈ (Fil (n : ℤ)).S T := by
    induction n with
    | zero =>
      rw [hF.top ((0 : ℕ) : ℤ) (by simp) T]
      exact Submodule.mem_top
    | succ n ih =>
      rw [Fin.prod_univ_succ]
      simpa only [Nat.add_comm 1 n] using
        hF.mul 1 n T (hf 0) (ih (fun k => f k.succ) fun k => hf k.succ)
  refine hF.mul j q _ (prod_fil_mem _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _
end
end
