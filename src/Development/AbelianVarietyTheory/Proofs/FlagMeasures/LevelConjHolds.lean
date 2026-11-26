module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicFrameLevelConjFormLevelWithCharacters
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemColumnLevelIffMemLinkedFrameLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameAdelicColumnLatticeLinkedReference
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsSpanAdelicLatticeModLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicEmbeddingBasisLiesInModule
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicEmbeddingBasisLiesInModule
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.TransportCong


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem inModL_of_inMod_embA : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), InMod X.B.I X.B.g (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) (embA X wt ιA y) → InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  intro D X u wt ιA hW hA b bd y hy
  obtain ⟨h1, -, hinj, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA
  have hadd : ∀ x x', embA X wt ιA (x + x') = embA X wt ιA x + embA X wt ιA x' := by
    intro x x'; simp only [embA, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : D.host.E ⊗[D.host.F] Ad D.host.F) x,
      embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
    intro c x; simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  have hzero : embA X wt ιA 0 = 0 := by simp [embA]
  have hsub : ∀ x x', embA X wt ιA (x - x') = embA X wt ιA x - embA X wt ιA x' := by
    intro x x'
    have := hadd (x - x') x'
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have hS : (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) =
      embA X wt ιA '' (Set.range b ∪ Set.range bd) := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]; rfl
  have hspan : ∀ s ∈ Submodule.span (IntAf X.B.I.F X.B.I.E) (embA X wt ιA '' (Set.range b ∪ Set.range bd)),
      ∃ s' ∈ Submodule.span (OAd D.host.F D.host.E) (Set.range b ∪ Set.range bd), embA X wt ιA s' = s := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx => obtain ⟨t, ht, rfl⟩ := hx; exact ⟨t, Submodule.subset_span ht, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, hzero⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      obtain ⟨s2, hs2, rfl⟩ := ihx'
      exact ⟨s1 + s2, Submodule.add_mem _ hs1 hs2, hadd _ _⟩
    | smul a x _ ihx =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      have ha : ιA (a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E := (hA.2 a).1 a.2
      refine ⟨(⟨_, ha⟩ : OAd D.host.F D.host.E) • s1, Submodule.smul_mem _ _ hs1, ?_⟩
      rw [Subring.smul_def, hsmul, RingEquiv.symm_apply_apply, Subring.smul_def]
  have hmL : ∀ w ∈ mL X.B.I X.B.g, ∃ x ∈ X.B.I.Lf,
      w = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨x', hx', rfl⟩ := hx; exact ⟨x', hx', rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, (smul_zero _).symm⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      obtain ⟨a2, h2, rfl⟩ := ihx'
      exact ⟨a1 + a2, Submodule.add_mem _ h1 h2, (smul_add _ _ _).symm⟩
    | smul a x _ ihx =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      refine ⟨a • a1, Submodule.smul_mem _ _ h1, ?_⟩
      simp only [Subring.smul_def, smul_smul, mul_comm]
  unfold InMod at hy
  rw [hS] at hy
  obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp hy
  obtain ⟨s', hs', rfl⟩ := hspan s hs
  obtain ⟨x, hx, rfl⟩ := hmL w hw
  rw [X.g_eq] at hsw
  rcases Nat.eq_zero_or_pos (D.host.g 0 * D.host.g 1) with h0 | hpos
  · refine ⟨s', hs', 0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero, add_zero]
    apply hinj
    rw [← hsw, h0, Nat.cast_zero, zero_smul, add_zero]
  · have hu : IsUnit (((D.host.g 0 * D.host.g 1 : ℕ)) : D.host.E ⊗[D.host.F] Ad D.host.F) := by
      rw [← map_natCast (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')).map _
    obtain ⟨c, hc⟩ := hu
    refine ⟨s', hs', ((c⁻¹ : (D.host.E ⊗[D.host.F] Ad D.host.F)ˣ) : D.host.E ⊗[D.host.F] Ad D.host.F) • (y - s'), ?_, ?_⟩
    · rw [h1, hsmul, hsub, ← hsw, add_sub_cancel_left, smul_smul, ← map_natCast ιA.symm, ← hc,
        ← map_mul, Units.inv_mul, map_one, one_smul]
      exact hx
    · rw [smul_smul, ← hc, Units.mul_inv, one_smul, add_sub_cancel]

end GlobalTheory.St.G.TransportCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicEmbeddingBasisLiesInModuleStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_embedding_basis_lies_in_module : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), InMod X.B.I X.B.g (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) (embA X wt ιA y) → InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  first | exact @GlobalTheory.St.G.TransportCong.inModL_of_inMod_embA | exact GlobalTheory.St.G.TransportCong.inModL_of_inMod_embA | (intros; apply GlobalTheory.St.G.TransportCong.inModL_of_inMod_embA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTypeVectorsSpanFixedLatticeVectorModLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTypeVectorsSpanFixedLatticeVectorModLevel
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.SpanMoved

theorem natSmul_mem (I : AutInst) (T : Submodule (IntAf I.F I.E) (VA I)) (n : ℕ) {t : VA I} (ht : t ∈ T) :
    (n : I.E ⊗[I.F] Af I.F) • t ∈ T := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem ht n

def satG (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) :
    Submodule (IntAf I.F I.E) (VA I) where
  carrier := {x | ∃ N : ℕ, Nat.Coprime N g ∧ (N : I.E ⊗[I.F] Af I.F) • x ∈ T}
  zero_mem' := ⟨1, Nat.coprime_one_left g, by simp⟩
  add_mem' := by
    rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    refine ⟨N * M, Nat.coprime_mul_iff_left.2 ⟨hN, hM⟩, ?_⟩
    have e : ((N * M : ℕ) : I.E ⊗[I.F] Af I.F) • (x + y) =
        (M : I.E ⊗[I.F] Af I.F) • ((N : I.E ⊗[I.F] Af I.F) • x) +
          (N : I.E ⊗[I.F] Af I.F) • ((M : I.E ⊗[I.F] Af I.F) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (M : I.E ⊗[I.F] Af I.F)]
    rw [e]
    exact add_mem (natSmul_mem I T M hx) (natSmul_mem I T N hy)
  smul_mem' := by
    rintro r x ⟨N, hN, hx⟩
    refine ⟨N, hN, ?_⟩
    have e : (N : I.E ⊗[I.F] Af I.F) • (r • x) = r • ((N : I.E ⊗[I.F] Af I.F) • x) :=
      smul_comm _ _ _
    rw [e]
    exact T.smul_mem r hx

theorem mem_of_coprime_smul (I : AutInst) (g n : ℕ) (hn : Nat.Coprime n g)
    (T : Submodule (IntAf I.F I.E) (VA I)) (hT : mL I g ≤ T) {v : VA I} (hv : v ∈ I.Lf)
    (hnv : (n : I.E ⊗[I.F] Af I.F) • v ∈ T) : v ∈ T := by
  have hg : (g : ℤ) • v ∈ T := by
    have h : (g : I.E ⊗[I.F] Af I.F) • v ∈ mL I g := Submodule.subset_span ⟨v, hv, rfl⟩
    rw [Nat.cast_smul_eq_nsmul] at h
    rw [natCast_zsmul]
    exact hT h
  have hn' : (n : ℤ) • v ∈ T := by
    rw [Nat.cast_smul_eq_nsmul] at hnv
    rw [natCast_zsmul]
    exact hnv

  have key : v = Nat.gcdA n g • ((n : ℤ) • v) + Nat.gcdB n g • ((g : ℤ) • v) := by
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (Nat.gcdA n g), mul_comm (Nat.gcdB n g),
      ← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hn, Nat.cast_one, one_smul]
  rw [key]
  exact add_mem (zsmul_mem hn' _) (zsmul_mem hg _)

private theorem mem_satG_iff_exists_coprime_smul_mem (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) (x : VA I) :
    x ∈ satG I g T ↔ ∃ N : ℕ, Nat.Coprime N g ∧ (N : I.E ⊗[I.F] Af I.F) • x ∈ T := Iff.rfl

private theorem mem_satG_of_mem (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) {x : VA I}
    (hx : x ∈ T) : x ∈ satG I g T :=
  (mem_satG_iff_exists_coprime_smul_mem I g T x).2 ⟨1, Nat.coprime_one_left g, by rw [Nat.cast_one, one_smul]; exact hx⟩

private theorem map_mem_mL_of_preserves_Lf (I : AutInst) (g : ℕ) (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I)
    (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf) {x : VA I} (hx : x ∈ mL I g) : φ x ∈ mL I g := by
  have h : mL I g ≤ (mL I g).comap (φ.restrictScalars (IntAf I.F I.E)) := by
    conv_lhs => unfold mL
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show φ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ mL I g
    rw [φ.map_smul]
    exact Submodule.subset_span ⟨φ y, hφ y hy, rfl⟩
  exact h hx

theorem map_mem_satG (I : AutInst) (g : ℕ)
    (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I) (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf) (S S' : Set (VA I))
    (hS : ∀ s ∈ S, φ s ∈ satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g))
    {w : VA I} (hw : InMod I g S w) :
    φ w ∈ satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g) := by
  have hle : Submodule.span (IntAf I.F I.E) S ⊔ mL I g ≤
      (satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g)).comap (φ.restrictScalars (IntAf I.F I.E)) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro s hs
      exact hS s hs
    · intro x hx
      exact mem_satG_of_mem I g _ (Submodule.mem_sup_right (map_mem_mL_of_preserves_Lf I g φ hφ hx))
  exact hle hw

theorem map_inAt (I : AutInst) (g : ℕ)
    (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I) (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf)
    (T : Submodule (IntAf I.F I.E) (VA I)) (hT : mL I g ≤ T) {d : VA I} (hd : InAt I g g d) :
    φ d ∈ satG I g T := by
  obtain ⟨N, hN, hNd⟩ := hd
  refine (mem_satG_iff_exists_coprime_smul_mem I g T _).2 ⟨N, hN, ?_⟩
  rw [← φ.map_smul]
  exact hT (map_mem_mL_of_preserves_Lf I g φ hφ hNd)

theorem span_moved : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ v ∈ X.B.I.Lf, p v = v → InMod X.B.I X.B.g (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪ Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))) v := by
  intro D X u c p hc hpL hef hzR v hv hpv
  have hcg : Nat.Coprime c X.B.g := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hc, Nat.gcd_one_left]
  let V := X.B.I.fmat (X.xu u)

  let ψ : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I :=
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (p ∘ₗ Matrix.mulVecLin V)
  have hψ : ∀ y, ψ y = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (V *ᵥ y) := fun y => rfl
  have hVVi : ∀ y, V *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec]
    simp [V, Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv]
  have hK : ∀ y, y ∈ X.B.I.Lf ↔ V *ᵥ y ∈ X.B.I.Lf := X.xu_K u
  have hViL : ∀ y ∈ X.B.I.Lf, X.B.I.fmat (X.xu u)⁻¹ *ᵥ y ∈ X.B.I.Lf := fun y hy =>
    (hK _).2 (by rw [hVVi]; exact hy)
  have hψL : ∀ y ∈ X.B.I.Lf, ψ y ∈ X.B.I.Lf := fun y hy => by
    rw [hψ]
    exact hpL _ ((hK y).1 hy)
  let S' : Set (VA X.B.I) :=
    Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪
      Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))
  let T := Submodule.span (IntAf X.B.I.F X.B.I.E) S' ⊔ mL X.B.I X.B.g
  have hT : mL X.B.I X.B.g ≤ T := le_sup_right

  have hS : ∀ s ∈ Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd,
      ψ s ∈ satG X.B.I X.B.g T := by
    rintro s ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hs) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    ·
      have hfix : V *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := (X.xu_fix u a).1
      have h0 : ψ (incl X.B.I (X.eR a)) = 0 := by rw [hψ, hfix, (hef a).1, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.e0 a - incl X.B.I (X.eR a)) := (X.basisApprox a).1
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rwa [map_sub, h0, sub_zero] at h
    ·
      have hfix : V *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
      have h0 : ψ (incl X.B.I (X.fR a)) = 0 := by rw [hψ, hfix, (hef a).2, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.f0 a - incl X.B.I (X.fR a)) := (X.basisApprox a).2
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rwa [map_sub, h0, sub_zero] at h
    ·
      rw [Set.mem_singleton_iff] at hs
      subst hs
      have h0 : ψ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = 0 := by
        rw [hψ, hVVi, hzR, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) :=
        X.xu_z u
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rw [map_sub, h0, zero_sub] at h
      simpa using neg_mem h
    · exact mem_satG_of_mem X.B.I X.B.g T
        (Submodule.mem_sup_left (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
    · exact mem_satG_of_mem X.B.I X.B.g T
        (Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))

  have hmap := map_mem_satG X.B.I X.B.g ψ hψL _ S' hS (X.latticeSpan _ (hViL v hv))
  obtain ⟨N, hN, hNv⟩ := (mem_satG_iff_exists_coprime_smul_mem _ _ _ _).1 hmap
  rw [hψ, hVVi, hpv, smul_smul, ← Nat.cast_mul] at hNv
  exact mem_of_coprime_smul X.B.I X.B.g (N * c) (Nat.Coprime.mul_left hN hcg) T hT hv hNv

end GlobalTheory.St.G.SpanMoved
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTypeVectorsSpanFixedLatticeVectorModLevelStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_type_vectors_span_fixed_lattice_vector_mod_level : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ v ∈ X.B.I.Lf, p v = v → InMod X.B.I X.B.g (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪ Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))) v := by
  first | exact @GlobalTheory.St.G.SpanMoved.span_moved | exact GlobalTheory.St.G.SpanMoved.span_moved | (intros; apply GlobalTheory.St.G.SpanMoved.span_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsSpanAdelicLatticeModLevel
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameSpan

theorem span_mod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ x, p (embA X wt ιA x) = embA X wt ιA x) → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → ∀ y ∈ hat D.host.F (Mq wt), InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  intro D X u wt ιA hW hI c p hc hp hpL hef hz b bd hb hbd y hy
  have h1 := (GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI).1
  have hv : embA X wt ιA y ∈ X.B.I.Lf := (h1 y).1 hy
  have hA := GlobalTheory.T.moved_type_vectors_span_fixed_lattice_vector_mod_level D X u c p hc hpL hef hz _ hv (hp y)
  have e1 : (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i))) =
      Set.range (fun i => embA X wt ιA (b i)) := by
    congr 1; funext i; exact (hb i).symm
  have e2 : (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))) =
      Set.range (fun i => embA X wt ιA (bd i)) := by
    congr 1; funext i; exact (hbd i).symm
  rw [e1, e2] at hA
  exact GlobalTheory.T.adelic_embedding_basis_lies_in_module D X u wt ιA hW hI b bd y hA

end GlobalTheory.St.G.FrameSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsSpanAdelicLatticeModLevelStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedTypeVectors_span_adelicLattice_modLevel : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ x, p (embA X wt ιA x) = embA X wt ιA x) → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → ∀ y ∈ hat D.host.F (Mq wt), InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  first | exact @GlobalTheory.St.G.FrameSpan.span_mod | exact GlobalTheory.St.G.FrameSpan.span_mod | (intros; apply GlobalTheory.St.G.FrameSpan.span_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsFixedByChosenPlacesIdempot
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsFixedByChosenPlacesIdempot
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameEps

theorem beps : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, b i = ιA X.ew • b i) ∧ ∀ i, bd i = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) • bd i := by
  intro D X u wt ιA hW hA c p b bd hb hbd
  have hinj := (GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA).2.2.1
  have semi : ∀ a x, embA X wt ιA (ιA a • x) = a • embA X wt ιA x := by
    intro a x
    simp only [embA, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, map_mul,
      RingEquiv.symm_apply_apply, mul_smul]
  constructor
  · intro i
    apply hinj
    rw [semi, hb, smul_comm X.ew, ← map_smul p X.ew, ← Matrix.mulVec_smul _ X.ew, ← X.bw_w i]
  · intro i
    apply hinj
    have hs : Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) = ιA (sigA X.B.I X.ew) :=
      (GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hA X.ew).symm
    rw [hs, semi, hbd, smul_comm (sigA X.B.I X.ew), ← map_smul p (sigA X.B.I X.ew),
      ← Matrix.mulVec_smul _ (sigA X.B.I X.ew), ← X.bwd_w i]

end GlobalTheory.St.G.FrameEps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsFixedByChosenPlacesIdempotStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_type_vectors_fixed_by_chosen_places_idempotent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, b i = ιA X.ew • b i) ∧ ∀ i, bd i = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) • bd i := by
  first | exact @GlobalTheory.St.G.FrameEps.beps | exact GlobalTheory.St.G.FrameEps.beps | (intros; apply GlobalTheory.St.G.FrameEps.beps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsDualModLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsDualModLevel
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.DualMod

open Formalism.L2.SG.Pf.unitaryCongruence

section Gen

variable (I : AutInst)

theorem hform_mulVec_conj {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have hd : ∀ (J : Matrix n n A) (x y : n → A), Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
    intro J x y
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [hd, hd, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

theorem hA_unitary (x : I.Gf) (u v : VA I) : hA I (I.fmat x *ᵥ u) (I.fmat x *ᵥ v) = hA I u v := by
  have h : Formalism.UG.cT (sigA I) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  unfold hA
  rw [hform_mulVec_conj, h]

theorem zmod_add {g : ℕ} {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) :
    ZMod' I g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, add_mem hs ht, by ring⟩

theorem zmod_mul {g : ℕ} {a c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) (ha : ZMod' I g a) :
    ZMod' I g (c * a) := by
  obtain ⟨s, hs, rfl⟩ := ha
  exact ⟨c * s, mul_mem hc hs, by ring⟩

theorem zmod_zero (g : ℕ) : ZMod' I g 0 := ⟨0, zero_mem _, by simp⟩

theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by simp [hA, Formalism.UG.hform]
theorem hA_zero_right (y : VA I) : hA I y 0 = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_mL_left {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I m y) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_left, map_natCast]
    exact ⟨hA I x y, hA_int I hx hy, rfl⟩
  | zero => rw [hA_zero_left]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_left]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I ((c : I.E ⊗[I.F] Af I.F) • a) y)
    rw [hA_smul_left]; exact zmod_mul I (sigA_mem I c.2) ha

theorem hA_mL_right {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I y m) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_right]
    exact ⟨hA I y x, hA_int I hy hx, rfl⟩
  | zero => rw [hA_zero_right]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_right]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I y ((c : I.E ⊗[I.F] Af I.F) • a))
    rw [hA_smul_right]; exact zmod_mul I c.2 ha

theorem mL_le (g : ℕ) : mL I g ≤ I.Lf := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact I.Lf.nsmul_mem hx g

end Gen

theorem dual_mod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) → ∀ i j, ∃ t ∈ OAd D.host.F D.host.E, hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) (bd i) (b j) - (if i = j then ιA X.ew else 0) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) * t := by
  intro D X u wt ιA hW hι c p b bd hb hbd hm i j
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hι
  have hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).1
  have hYd : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).2
  have hm1 : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j ∈ mL X.B.I X.B.g := by
    rw [hb j]; exact (hm j).1
  have hm2 : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g := by
    rw [hbd i]; exact (hm i).2
  have key : ZMod' X.B.I X.B.g
      (hA X.B.I (embA X wt ιA (bd i)) (embA X wt ιA (b j)) - if i = j then X.ew else 0) := by
    generalize hm' : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j = m' at hm1
    generalize hmm : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i = m at hm2
    have e1 : embA X wt ιA (b j) = X.B.I.fmat (X.xu u) *ᵥ X.bw j + m' := by rw [← hm']; abel
    have e2 : embA X wt ιA (bd i) = X.B.I.fmat (X.xu u) *ᵥ X.bwd i + m := by rw [← hmm]; abel
    rw [e1, e2, hA_add_left, hA_add_right, hA_add_right, hA_unitary]
    have e3 : hA X.B.I (X.bwd i) (X.bw j) + hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
        (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') - (if i = j then X.ew else 0) =
        (hA X.B.I (X.bwd i) (X.bw j) - (if i = j then X.ew else 0)) +
          hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
          (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') := by ring
    rw [e3]
    refine zmod_add _ (zmod_add _ (X.bw_dual i j) (hA_mL_right _ hm1 (hYd i)))
      (zmod_add _ (hA_mL_left _ hm2 (hY j)) (hA_mL_left _ hm2 (mL_le _ _ hm1)))
  obtain ⟨t, ht, he⟩ := key
  refine ⟨ιA t, (hι.2 t).1 ht, ?_⟩
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) =
      ιA (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [map_natCast, X.g_eq]
  have hif : (if i = j then ιA X.ew else 0) = ιA (if i = j then X.ew else 0) := by
    split_ifs <;> simp
  rw [← h2, hg, hif, ← map_sub, he, map_mul]

end GlobalTheory.St.G.DualMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsDualModLevelStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_type_vectors_dual_mod_level : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) → ∀ i j, ∃ t ∈ OAd D.host.F D.host.E, hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) (bd i) (b j) - (if i = j then ιA X.ew else 0) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) * t := by
  first | exact @GlobalTheory.St.G.DualMod.dual_mod | exact GlobalTheory.St.G.DualMod.dual_mod | (intros; apply GlobalTheory.St.G.DualMod.dual_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnsLatticeDivisibleByLevelAwayChosen
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnsLatticeDivisibleByLevelAwayChosen
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameFull

variable {D : D7}

theorem mL_div (I : Formalism.MainNotions.S.AutInst) (m : ℕ) :
    ∀ v ∈ mL I m, ∃ z ∈ I.Lf, v = (m : I.E ⊗[I.F] Af I.F) • z := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, I.Lf.zero_mem, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, I.Lf.add_mem ha hb, (smul_add _ _ _).symm⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, I.Lf.smul_mem c ha, smul_comm _ _ _⟩

theorem embA_smul (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
  simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem embA_zero (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA 0 = 0 := by
  simp [embA]

theorem step (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (hmem : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf)
    (hinj : Function.Injective (embA X wt ιA))
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F)
    (m : ℕ) (w : VA X.B.I) (hw : w ∈ X.B.I.Lf)
    (hwe : embA X wt ιA (c • y) = (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w) :
    ∃ z ∈ hat D.host.F (Mq wt), c • y = (m : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero]
    apply hinj
    rw [hwe, embA_zero, Nat.cast_zero, zero_smul]
  · have hF : IsUnit ((m : D.host.F)) := (Nat.cast_ne_zero.mpr hm.ne').isUnit
    have hR : IsUnit ((m : D.host.E ⊗[D.host.F] Ad D.host.F)) := by
      simpa using hF.map (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))
    obtain ⟨t, ht⟩ := hR.exists_right_inv
    refine ⟨t • (c • y), ?_, ?_⟩
    · rw [hmem, embA_smul, hwe, smul_smul, ← map_natCast ιA.symm m, ← map_mul, mul_comm, ht, map_one, one_smul]
      exact hw
    · rw [smul_smul, ht, one_smul]

theorem symm_unit (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA) :
    ιA.symm (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) =
      1 - X.ew - sigA X.B.I X.ew := by
  have h := GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hI X.ew
  apply ιA.injective
  rw [RingEquiv.apply_symm_apply, map_sub, map_sub, map_one]
  exact congrArg (fun t => 1 - ιA X.ew - t) h.symm

theorem emb_mem (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA)
    (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (hy : embA X wt ιA y ∈ X.B.I.Lf) :
    ∃ w ∈ X.B.I.Lf, embA X wt ιA
      ((1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y) =
      ((D.host.g 0 * D.host.g 1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w := by
  rw [embA_smul, symm_unit X ιA hI]
  obtain ⟨w, hw, hw'⟩ := mL_div X.B.I X.B.g _ (X.ew_full _ hy)
  exact ⟨w, hw, by rw [hw', X.g_eq]⟩

theorem eps_full : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ y ∈ hat D.host.F (Mq wt), ∃ z ∈ hat D.host.F (Mq wt), (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  intro D X u wt ιA hW hI y hy
  obtain ⟨hmem, -, hinj, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  obtain ⟨w, hw, hwe⟩ := emb_mem X wt ιA hI y ((hmem y).1 hy)
  exact step X wt ιA hmem hinj _ y _ w hw hwe

end GlobalTheory.St.G.FrameFull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnsLatticeDivisibleByLevelAwayChosenStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_columns_lattice_divisible_by_level_away_chosen : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ y ∈ hat D.host.F (Mq wt), ∃ z ∈ hat D.host.F (Mq wt), (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  first | exact @GlobalTheory.St.G.FrameFull.eps_full | exact GlobalTheory.St.G.FrameFull.eps_full | (intros; apply GlobalTheory.St.G.FrameFull.eps_full <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameAdelicColumnLatticeLinkedReference
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameLink

theorem frame_exists : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ Fr : FrQ D wt, FrLink X u wt ιA Fr := by
  intro D X u wt ιA hW hI
  obtain ⟨c, p, hc, hrng, hid, hLf, hkill, hkz, hcl⟩ := GlobalTheory.T.exists_coprime_projection_adelic_lattice_into_columns D X u wt ιA hW hI
  have hmhat := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  have hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf ∧ X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf := fun i =>
    ⟨(X.xu_K u (X.bw i)).1 (X.vectorsInLattice.2.2 i).1, (X.xu_K u (X.bwd i)).1 (X.vectorsInLattice.2.2 i).2⟩
  have hb0 : ∀ i, ∃ x, embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) := fun i => by
    obtain ⟨x, hx⟩ := hrng ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.bw i))
    exact ⟨x, by rw [← hx, map_smul]⟩
  have hbd0 : ∀ i, ∃ x, embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) := fun i => by
    obtain ⟨x, hx⟩ := hrng ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))
    exact ⟨x, by rw [← hx, map_smul]⟩
  choose b hb using hb0
  choose bd hbd using hbd0
  have hclose := GlobalTheory.T.projection_moves_typeVectors_modLevel D X u wt ιA hW hI c p hcl
  have hbe := GlobalTheory.T.transported_type_vectors_fixed_by_chosen_places_idempotent D X u wt ιA hW hI c p b bd hb hbd
  refine ⟨{ eps := ιA X.ew
            eps_idem := by rw [← map_mul, X.ew_idem]
            eps_orth := by rw [← GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hI, ← map_mul, X.ew_orth, map_zero]
            eps_int := (hI.2 _).1 X.ew_int
            eps_full := GlobalTheory.T.adelic_columns_lattice_divisible_by_level_away_chosen D X u wt ιA hW hI
            b := b
            bd := bd
            b_mem := fun i => (hmhat.1 (b i)).2 (by rw [hb i]; exact hLf _ (hY i).1)
            bd_mem := fun i => (hmhat.1 (bd i)).2 (by rw [hbd i]; exact hLf _ (hY i).2)
            b_eps := hbe.1
            bd_eps := hbe.2
            dual := GlobalTheory.T.transported_type_vectors_dual_mod_level D X u wt ιA hW hI c p b bd hb hbd hclose
            span := GlobalTheory.T.transportedTypeVectors_span_adelicLattice_modLevel D X u wt ιA hW hI c p hc hid hLf hkill hkz b bd hb hbd
            psi := fun a => X.psiEf (ιA.symm a)
            psi_add := fun x y => by
              show X.psiEf (ιA.symm (x + y)) = X.psiEf (ιA.symm x) * X.psiEf (ιA.symm y)
              rw [RingEquiv.map_add (e := _), X.psiEf_add]
            psi_int := fun x hx => X.psiEf_int _ ((hI.2 _).2 (by simpa using hx))
            psi_rat := GlobalTheory.T.transportedFiniteCharacter_inverse_exp_trace D X ιA hI }, rfl, fun i => ?_, fun i => ?_, fun a => rfl⟩
  · show embA X wt ιA (b i) - _ ∈ _
    rw [hb i]; exact (hclose i).1
  · show embA X wt ιA (bd i) - _ ∈ _
    rw [hbd i]; exact (hclose i).2

end GlobalTheory.St.G.FrameLink
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameAdelicColumnLatticeLinkedReferenceStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_adelicColumnLattice_linked_reference : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ Fr : FrQ D wt, FrLink X u wt ιA Fr := by
  first | exact @GlobalTheory.St.G.FrameLink.frame_exists | exact GlobalTheory.St.G.FrameLink.frame_exists | (intros; apply GlobalTheory.St.G.FrameLink.frame_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicCorrectionLevelCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportFrameAlongUnitaryAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportFrameAlongUnitaryAdelic
noncomputable section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.FrMap

theorem hform_eq_dot {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) : hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J M : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) : hform s J (M *ᵥ x) (M *ᵥ y) = hform s (cT s M * J * M) x y := by
  rw [hform_eq_dot, hform_eq_dot]
  have h1 : (fun i => s ((M *ᵥ x) i)) = (M.map s) *ᵥ (fun i => s (x i)) := by
    funext i; simp [mulVec, dotProduct, map_sum]
  rw [h1, cT, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm, dotProduct_mulVec,
    dotProduct_comm]

theorem inModL_map {A : Type} [CommRing A] {O : Subring A} {n : ℕ} {Λ Λ' : Submodule O (Fin n → A)} (m : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (hP : ∀ z ∈ Λ, P *ᵥ z ∈ Λ') {S S' : Set (Fin n → A)}
    (hS : ∀ s ∈ S, P *ᵥ s ∈ S') {x : Fin n → A} (hx : InModL Λ m S x) : InModL Λ' m S' (P *ᵥ x) := by
  obtain ⟨s, hs, z, hz, rfl⟩ := hx
  let f : (Fin n → A) →ₗ[O] (Fin n → A) := (Matrix.mulVecLin P).restrictScalars O
  refine ⟨P *ᵥ s, ?_, P *ᵥ z, hP z hz, by rw [mulVec_add, mulVec_smul]⟩
  have : f s ∈ Submodule.span O (f '' S) := by
    rw [← Submodule.map_span]; exact Submodule.mem_map_of_mem hs
  exact Submodule.span_mono (by rintro _ ⟨t, ht, rfl⟩; exact hS t ht) this

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) (h : UPts σ J (Ad F)), (∀ x, (h⁻¹).1.1 *ᵥ x ∈ Λ' ↔ x ∈ Λ) → ∀ Fr : AdFrame σ J Λ g k, ∃ Fr' : AdFrame σ J Λ' g k, ∀ y : UPts σ J (Ad F), (Fr.InK y.1 ↔ Fr'.InK (h⁻¹ * y * h : UPts σ J (Ad F)).1) ∧ Fr.chi y.1 = Fr'.chi (h⁻¹ * y * h : UPts σ J (Ad F)).1 := by
  intro F E _ _ _ _ _ n σ J Λ Λ' g k h hΛ Fr
  set M : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := h.1.1 with hM
  set Mi : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := (h⁻¹).1.1 with hMi
  have hMMi : M * Mi = 1 := by
    rw [hM, hMi]; show (h.1 * h.1⁻¹).val = 1; rw [mul_inv_cancel]; rfl
  have hMiM : Mi * M = 1 := by
    rw [hM, hMi]; show (h.1⁻¹ * h.1).val = 1; rw [inv_mul_cancel]; rfl
  have hinvM : ∀ u v, hR σ J (Ad F) (M *ᵥ u) (M *ᵥ v) = hR σ J (Ad F) u v := by
    intro u v; unfold hR; rw [hform_mulVec]; congr 1; exact h.2
  have hinvMi : ∀ u v, hR σ J (Ad F) (Mi *ᵥ u) (Mi *ᵥ v) = hR σ J (Ad F) u v := by
    intro u v; unfold hR; rw [hform_mulVec]; congr 1; exact (h⁻¹).2
  have hΛ'' : ∀ x, x ∈ Λ' ↔ M *ᵥ x ∈ Λ := by
    intro x; rw [← hΛ (M *ᵥ x), mulVec_mulVec, hMiM, one_mulVec]
  have hMiΛ : ∀ z ∈ Λ, Mi *ᵥ z ∈ Λ' := fun z hz => (hΛ z).2 hz
  have hMΛ' : ∀ z ∈ Λ', M *ᵥ z ∈ Λ := fun z hz => (hΛ'' z).1 hz
  have hMMiv : ∀ v, M *ᵥ (Mi *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hMMi, one_mulVec]
  have hMiMv : ∀ v, Mi *ᵥ (M *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hMiM, one_mulVec]
  let Fr' : AdFrame σ J Λ' g k :=
    { eps := Fr.eps, eps_idem := Fr.eps_idem, eps_orth := Fr.eps_orth, eps_int := Fr.eps_int,
      eps_full := by
        intro y hy
        obtain ⟨z, hz, e⟩ := Fr.eps_full (M *ᵥ y) (hMΛ' y hy)
        refine ⟨Mi *ᵥ z, hMiΛ z hz, ?_⟩
        have := congrArg (Mi *ᵥ ·) e
        simp only [mulVec_smul, hMiMv] at this
        exact this
      b := fun i => Mi *ᵥ Fr.b i, bd := fun i => Mi *ᵥ Fr.bd i,
      b_mem := fun i => hMiΛ _ (Fr.b_mem i), bd_mem := fun i => hMiΛ _ (Fr.bd_mem i),
      b_eps := fun i => by
        show Mi *ᵥ Fr.b i = Fr.eps • (Mi *ᵥ Fr.b i)
        rw [← mulVec_smul, ← Fr.b_eps i]
      bd_eps := fun i => by
        show Mi *ᵥ Fr.bd i = sigR σ (Ad F) Fr.eps • (Mi *ᵥ Fr.bd i)
        rw [← mulVec_smul, ← Fr.bd_eps i]
      dual := fun i j => by
        show ∃ t ∈ OAd F E, hR σ J (Ad F) (Mi *ᵥ Fr.bd i) (Mi *ᵥ Fr.b j) - _ = _
        rw [hinvMi]; exact Fr.dual i j
      span := by
        intro y hy
        have := inModL_map g Mi hMiΛ (S' := Set.range (fun i => Mi *ᵥ Fr.b i) ∪ Set.range (fun i => Mi *ᵥ Fr.bd i))
          (by rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩); exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩])
          (Fr.span (M *ᵥ y) (hMΛ' y hy))
        rwa [hMiMv] at this
      psi := Fr.psi, psi_add := Fr.psi_add, psi_int := Fr.psi_int, psi_rat := Fr.psi_rat }
  refine ⟨Fr', fun y => ?_⟩
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := y.1.1 with hY
  have hconj : ((h⁻¹ * y * h : UPts σ J (Ad F)).1 : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F)) = Mi * Y * M := rfl
  have hc1 : M * (Mi * Y * M) = Y * M := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMMi, Matrix.one_mul]
  have hc3 : M * (Mi * Y * M - 1) = (Y - 1) * M := by
    rw [Matrix.mul_sub, hc1, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
  have hc4 : (Mi * Y * M - 1) * Mi = Mi * (Y - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hMMi, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hc5 : (Mi * Y * M) * Mi = Mi * Y := by
    rw [Matrix.mul_assoc, hMMi, Matrix.mul_one]
  constructor
  · unfold AdFrame.InK
    rw [hconj]
    have key1 : ∀ x, (Mi * Y * M) *ᵥ x ∈ Λ' ↔ Y *ᵥ (M *ᵥ x) ∈ Λ := by
      intro x; rw [hΛ'', mulVec_mulVec, hc1, ← mulVec_mulVec]
    have key2 : ∀ x, (Mi * Y * M - 1) *ᵥ x ∈ Λ' ↔ (Y - 1) *ᵥ (M *ᵥ x) ∈ Λ := by
      intro x; rw [hΛ'', mulVec_mulVec, hc3, ← mulVec_mulVec]
    have keyd : ∀ x, (∀ z ∈ Λ', hR σ J (Ad F) z x ∈ OAd F E) ↔ (∀ z ∈ Λ, hR σ J (Ad F) z (M *ᵥ x) ∈ OAd F E) := by
      intro x; constructor
      · intro H z hz; have := H _ (hMiΛ z hz); rwa [← hinvM, hMMiv] at this
      · intro H z hz; have := H _ (hMΛ' z hz); rwa [hinvM] at this
    refine and_congr ?_ (and_congr ?_ ?_)
    · show (∀ x, x ∈ Λ ↔ Y *ᵥ x ∈ Λ) ↔ (∀ x, x ∈ Λ' ↔ (Mi * Y * M) *ᵥ x ∈ Λ')
      constructor
      · intro H x; rw [hΛ'', key1]; exact H _
      · intro H x; have := H (Mi *ᵥ x); rwa [hΛ'', key1, hMMiv] at this
    · constructor
      · intro H x hx; rw [key2]; exact H _ ((keyd x).1 hx)
      · intro H x hx
        have := H (Mi *ᵥ x) ((keyd _).2 (by rwa [hMMiv]))
        rwa [key2, hMMiv] at this
    · refine forall_congr' fun i => ?_
      show _ ↔ InModL Λ' g ((fun j => Mi *ᵥ Fr.b j) '' {j | j.1 < i.1}) ((Mi * Y * M - 1) *ᵥ (Mi *ᵥ Fr.b i))
      rw [mulVec_mulVec, hc4, ← mulVec_mulVec]
      constructor
      · intro H
        exact inModL_map g Mi hMiΛ (by rintro _ ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩) H
      · intro H
        have := inModL_map g M hMΛ' (S' := Fr.b '' {j | j.1 < i.1})
          (by rintro _ ⟨j, hj, rfl⟩; exact ⟨j, hj, (hMMiv _).symm⟩) H
        rwa [hMMiv] at this
  · unfold AdFrame.chi
    rw [hconj]
    show Fr.psi _ = Fr.psi _
    congr 2
    unfold supSum
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · show hR σ J (Ad F) (Fr.bd i) (Y *ᵥ Fr.b _) = hR σ J (Ad F) (Mi *ᵥ Fr.bd i) ((Mi * Y * M) *ᵥ (Mi *ᵥ Fr.b _))
      rw [mulVec_mulVec, hc5, ← mulVec_mulVec, hinvMi]
    · rfl

end GlobalTheory.St.G.FrMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportFrameAlongUnitaryAdelicStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_frame_along_unitary_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) (h : UPts σ J (Ad F)), (∀ x, (h⁻¹).1.1 *ᵥ x ∈ Λ' ↔ x ∈ Λ) → ∀ Fr : AdFrame σ J Λ g k, ∃ Fr' : AdFrame σ J Λ' g k, ∀ y : UPts σ J (Ad F), (Fr.InK y.1 ↔ Fr'.InK (h⁻¹ * y * h : UPts σ J (Ad F)).1) ∧ Fr.chi y.1 = Fr'.chi (h⁻¹ * y * h : UPts σ J (Ad F)).1 := by
  first | exact @GlobalTheory.St.G.FrMap.transport | exact GlobalTheory.St.G.FrMap.transport | (intros; apply GlobalTheory.St.G.FrMap.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicCorrectionLevelCharacter
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.level_char_match : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (Fr : AdFrame cm.sig J Λ (gp 0 * gp 1) k) (h0 : UPts cm.sig J (Ad F)), (∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) → ∃ h1 : UPts cm.sig J (Ad F), (∀ x, (h1⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Λ Fr h0 hh0
  obtain ⟨Fr', hFr'⟩ := GlobalTheory.T.transport_frame_along_unitary_adelic F E n cm.sig J Λ (hat F S.Lb) (gp 0 * gp 1) k h0 hh0 Fr
  obtain ⟨κ, hκ, hκU⟩ := GlobalTheory.T.adelicFrameLevel_conj_formLevel_with_characters F E cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Fr'
  refine ⟨h0 * κ, ?_, ?_⟩
  · intro x
    have hκi : (κ⁻¹ : UPts cm.sig J (Ad F)).1 ∈ stabGL (hat F S.Lb) := by
      simpa using (stabGL (hat F S.Lb)).inv_mem hκ
    have e : ((h0 * κ)⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x = (κ⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ ((h0⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x) := by
      rw [_root_.mul_inv_rev]; simp [Matrix.mulVec_mulVec]
    rw [e, ← hκi _, hh0]
  · intro y
    have e : ((h0 * κ)⁻¹ * y * (h0 * κ) : UPts cm.sig J (Ad F)) = κ⁻¹ * (h0⁻¹ * y * h0) * κ := by group
    obtain ⟨h1, h2⟩ := hFr' y
    obtain ⟨h3, h4⟩ := hκU (h0⁻¹ * y * h0)
    refine ⟨?_, ?_⟩
    · rw [h1, h3, e]
    · intro hy
      rw [h2]
      have hy' : ((κ⁻¹ * (h0⁻¹ * y * h0) * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U := by rw [← e]; exact hy
      rw [h4 hy']
      have hx : (⟨_, hy'⟩ : S.U) = ⟨_, hy⟩ := Subtype.ext (congrArg (fun z : UPts cm.sig J (Ad F) => z.1) e.symm)
      rw [hx]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicCorrectionLevelCharacterStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_correction_level_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (Fr : AdFrame cm.sig J Λ (gp 0 * gp 1) k) (h0 : UPts cm.sig J (Ad F)), (∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) → ∃ h1 : UPts cm.sig J (Ad F), (∀ x, (h1⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.St.G.level_char_match | exact GlobalTheory.St.G.level_char_match | (intros; apply GlobalTheory.St.G.level_char_match <;> assumption)
end
end

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem levelConj_holds : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), LevelConj D F := by
  intro D F X hK u wt ιA h0 hW hI hL
  obtain ⟨Fr, hFr⟩ := GlobalTheory.T.exists_frame_adelicColumnLattice_linked_reference D X u wt ιA hW hI
  obtain ⟨hMq, -, -, -, -, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  obtain ⟨hT, hg, hTg, hf, hNk, hH, hdet⟩ := record_facts D u
  have hΛ : ∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat D.host.F (F u).cls0.lev.Lb ↔ x ∈ hat D.host.F (Mq wt) := by
    intro x
    rw [hMq x]
    exact hL x
  obtain ⟨h1, hL1, hK1⟩ := GlobalTheory.T.exists_adelic_correction_level_character D.host.F D.host.E D.sp.cm (D.R.N 0) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) hH hdet
    (D.mem u).A.T D.R.f D.R.t D.R.k D.R.k D.R.k (D.R.N 0) D.host.g (F u).cls0.lev (F u).gl (F u).glev0
    hNk.symm hNk.symm hNk.symm rfl (D.mem u).A.T_prime D.host.g_prime D.host.g_ne hTg hg hT hf
    (hat D.host.F (Mq wt)) Fr h0 hΛ
  refine ⟨h1, fun x => ?_, fun h y hy => ?_⟩
  · exact (hL1 x).trans (hMq x)
  · have hin := GlobalTheory.T.mem_columnLevel_iff_mem_linkedFrameLevel D X u wt ιA hW hI hK Fr hFr h y hy
    have hch := GlobalTheory.T.columns_character_eq_linked_frame_character D X u wt ιA hW hI hK Fr hFr h y hy
    refine ⟨hin.trans (hK1 y).1, fun hk hy' => ?_⟩
    rw [hch hk]
    exact (hK1 y).2 hy'

end GlobalTheory.St.G
