module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjArchUnipotentMemNhdsOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjArchUnipotentMemNhdsOne
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology Filter
open scoped NumberField.AdeleRing

namespace GlobalTheory.InfConj

theorem continuous_mixedSpace_symm (E : Type) [Field E] [NumberField E] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

def liftMat (E : Type) [Field E] [NumberField E] (a : ℕ)
    (Y : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E a) : Matrix (Fin a) (Fin a) (Ad E) :=
  Matrix.of fun i j => (((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (Y i j), 0) : Ad E)

theorem continuous_liftMat (E : Type) [Field E] [NumberField E] (a : ℕ) : Continuous (liftMat E a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.prodMk ((continuous_mixedSpace_symm E).comp ?_) continuous_const
  exact (continuous_apply j).comp (continuous_apply i)

theorem liftMat_zero (E : Type) [Field E] [NumberField E] (a : ℕ) : liftMat E a 0 = 0 := by
  ext i j : 2
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm 0 = 0
    exact map_zero _
  · rfl

theorem liftMat_archMat (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Ad E))
    (hZ : ∀ i j, (Z i j).2 = 0) : liftMat E a (GroundTheory.Automorphic.CuspidalSpectrum.archMat E a Z) = Z := by
  ext i j : 2
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (InfiniteAdeleRing.ringEquiv_mixedSpace E (Z i j).1) = (Z i j).1
    exact RingEquiv.symm_apply_apply _ _
  · exact (hZ i j).symm

end GlobalTheory.InfConj

namespace GlobalTheory.InfConj

theorem conj_blockEntry_snd (E : Type) [Field E] [NumberField E] (a r : ℕ) (x : GA E a)
    (P : BlockIx a r → Ad E) (hP : ∀ p, (P p).2 = 0) (i j : Fin a) :
    ((((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E))) i j).2 = 0 := by
  let f : Matrix (Fin a) (Fin a) (Ad E) →+* Matrix (Fin a) (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) :=
    (RingHom.snd (InfiniteAdeleRing E) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)).mapMatrix
  have hB : f (GroundTheory.Automorphic.AutomorphicForm.blockEntry P) = 0 := by
    refine Matrix.ext fun k l => ?_
    change (GroundTheory.Automorphic.AutomorphicForm.blockEntry P k l).2 = 0
    unfold GroundTheory.Automorphic.AutomorphicForm.blockEntry
    rw [Matrix.of_apply]
    split_ifs with h
    · exact hP _
    · rfl
  change f (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E))) i j = 0
  rw [map_mul, map_mul, hB, mul_zero, zero_mul]
  rfl

theorem conj_unip_mem_nhds : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := by
  intro E _ _ a r U hU
  rw [(Units.isInducing_embedProduct (M := Matrix (Fin a) (Fin a) (Ad E))).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  let φ : Matrix (Fin a) (Fin a) (Ad E) → Matrix (Fin a) (Fin a) (Ad E) × (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    fun Z => (1 + Z, MulOpposite.op (1 - Z))
  have hφ : Continuous φ :=
    (continuous_const.add continuous_id).prodMk (MulOpposite.continuous_op.comp (continuous_const.sub continuous_id))
  have hφ0 : φ (liftMat E a 0) = Units.embedProduct _ (1 : GA E a) := by
    rw [liftMat_zero]
    simp only [φ, add_zero, sub_zero, Units.embedProduct_apply, inv_one, Units.val_one]
  have hnb : (φ ∘ liftMat E a) ⁻¹' t ∈ 𝓝 (0 : GroundTheory.Automorphic.AutomorphicForm.ArchMatrix E a) :=
    (hφ.comp (continuous_liftMat E a)).continuousAt.preimage_mem_nhds (by
      rw [Function.comp_apply, hφ0]; exact ht)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnb
  refine ⟨ε / 2, by positivity, fun x P hP hnorm => htU ?_⟩
  set Z := ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
    GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)) with hZdef
  have hmem : GroundTheory.Automorphic.CuspidalSpectrum.archMat E a Z ∈ Metric.ball 0 ε := by
    rw [mem_ball_zero_iff]; linarith
  have h1 := hball hmem
  rw [Set.mem_preimage, Function.comp_apply, liftMat_archMat E a Z (conj_blockEntry_snd E a r x P hP)] at h1
  rw [Set.mem_preimage]
  convert h1 using 1
  have hv : ((x⁻¹ * unip P * x : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = 1 + Z := by
    rw [Units.val_mul, Units.val_mul]
    change ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 + nilM P) * (x : Matrix (Fin a) (Fin a) (Ad E)) = _
    rw [mul_add, add_mul, mul_one, Units.inv_mul, hZdef]
    rfl
  have hi : ((x⁻¹ * unip P * x : GA E a)⁻¹ : GA E a).val = 1 - Z := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul]
    change ((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) * (1 - nilM P) * (x : Matrix (Fin a) (Fin a) (Ad E)) = _
    rw [mul_sub, sub_mul, mul_one, Units.inv_mul, hZdef]
    rfl
  simp only [Units.embedProduct_apply, φ]
  rw [hv, hi]

end GlobalTheory.InfConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjArchUnipotentMemNhdsOneStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_archUnipotent_mem_nhds_one : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := by
  first | exact @GlobalTheory.InfConj.conj_unip_mem_nhds | exact GlobalTheory.InfConj.conj_unip_mem_nhds | (intros; apply GlobalTheory.InfConj.conj_unip_mem_nhds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompactDetBandSiegelSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompactDetBandSiegelSet
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

open scoped Pointwise

namespace GlobalTheory.SiegelBand

open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.IdeleGroup

theorem le_pow_mul_of_adjacent {a : ℕ} (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) {Q : ℝ} (hQ : 1 ≤ Q)
    (hadj : ∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ Q * ρ j ∧ ρ j ≤ Q * ρ i) (i j : Fin a) :
    ρ i ≤ Q ^ a * ρ j := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have key : ∀ m : ℕ, ∀ i j : Fin a, (j : ℕ) = i + m → ρ i ≤ Q ^ m * ρ j ∧ ρ j ≤ Q ^ m * ρ i := by
    intro m
    induction m with
    | zero =>
      intro i j h
      have : i = j := Fin.ext (by omega)
      subst this
      simp
    | succ m ih =>
      intro i j h
      let j' : Fin a := ⟨i + m, by omega⟩
      obtain ⟨h1, h2⟩ := ih i j' rfl
      obtain ⟨h3, h4⟩ := hadj j' j (by simp [j']; omega)
      have hpm : 0 ≤ Q ^ m := pow_nonneg hQ0 m
      constructor
      · calc ρ i ≤ Q ^ m * ρ j' := h1
          _ ≤ Q ^ m * (Q * ρ j) := mul_le_mul_of_nonneg_left h3 hpm
          _ = Q ^ (m + 1) * ρ j := by ring
      · calc ρ j ≤ Q * ρ j' := h4
          _ ≤ Q * (Q ^ m * ρ i) := mul_le_mul_of_nonneg_left h2 hQ0
          _ = Q ^ (m + 1) * ρ i := by ring
  rcases le_total (i : ℕ) j with hij | hij
  · have h := (key ((j : ℕ) - i) i j (by omega)).1
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by omega)) (hρ j).le)
  · have h := (key ((i : ℕ) - j) j i (by omega)).2
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by omega)) (hρ j).le)

theorem absDetA_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) :
    absDetA g = (ideleModule E (AdelicGLn.det E a g) : ℝ) := by
  unfold absDetA
  rw [Reduction.adeleAbs_units (K := E)]
  rfl

theorem posIdele_congr {E : Type} [Field E] [NumberField E] {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    Reduction.posIdele (K := E) x hx = Reduction.posIdele (K := E) y hy := by
  subst h; rfl

theorem exists_isCompact_band_siegel : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := by
  intro E _ _ a ω hω t R ht
  classical
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have hfc : Continuous fun b : GA E a => (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  obtain ⟨B₁, B₂, hB₁, hB₁₂, hB⟩ := Reduction.exists_pos_bounds hω hfc
    (fun b _ => (ideleModule E (AdelicGLn.det E a b)).2)
  have hB₂ : 0 < B₂ := hB₁.trans_le hB₁₂
  set X₁ : ℝ := min 1 B₂⁻¹ with hX₁def
  set X₂ : ℝ := max 1 (2 / B₁) with hX₂def
  have hX₁ : 0 < X₁ := lt_min one_pos (inv_pos.2 hB₂)
  set Q : ℝ := max 1 (max R t⁻¹) with hQdef
  have hQ : 1 ≤ Q := le_max_left _ _
  set Qa : ℝ := (Q ^ a) ^ a with hQadef
  have hQa : 0 < Qa := pow_pos (pow_pos (zero_lt_one.trans_le hQ) _) _
  set lo : ℝ := min 1 (X₁ / Qa) with hlodef
  set hi : ℝ := max 1 (Qa * X₂) with hhidef
  have hlo : 0 < lo := lt_min one_pos (div_pos hX₁ hQa)
  let g : {r : ℝ // 0 < r} → IdeleGroup E := fun r => Reduction.posIdele (K := E) r.1 r.2
  have hg : Continuous g := Reduction.continuous_posIdele_subtype
  let h : (Fin a → ℝ) → (Fin a → IdeleGroup E) := fun ρ i => g ⟨max (ρ i) lo, hlo.trans_le (le_max_right _ _)⟩
  have hh : Continuous h := continuous_pi fun i => hg.comp
      (((continuous_apply i).max continuous_const).subtype_mk fun ρ => hlo.trans_le (le_max_right _ _))
  let F : (Fin a → ℝ) → GA E a := fun ρ => Reduction.diagUnits a (h ρ)
  have hF : Continuous F := (Reduction.continuous_diagUnits (K := E) a).comp hh
  have hT : IsCompact (F '' Set.pi Set.univ (fun _ => Set.Icc lo hi)) := (isCompact_univ_pi fun _ => isCompact_Icc).image hF
  have hband : band E a = {g | 1 ≤ (ideleModule E (AdelicGLn.det E a g) : ℝ)} ∩
      {g | (ideleModule E (AdelicGLn.det E a g) : ℝ) ≤ 2} := by
    ext g; simp [band, absDetA_eq]
  have hclosed : IsClosed (band E a) := by
    rw [hband]; exact (isClosed_le continuous_const hfc).inter (isClosed_le hfc continuous_const)
  refine ⟨ω * (F '' Set.pi Set.univ (fun _ => Set.Icc lo hi)) * (Reduction.maxCompact (K := E) (n := a) : Set (GA E a)) ∩ band E a,
    ((hω.mul hT).mul Reduction.isCompact_maxCompact).inter_right hclosed, Set.inter_subset_right, ?_⟩
  intro b hb ρ hρ hlow hup k hk hmem
  refine ⟨?_, hmem⟩
  set P : ℝ := ∏ i, ρ i with hPdef
  have hP : 0 < P := Finset.prod_pos fun i _ => hρ i
  have hdet := Reduction.det_mul_mul b (Reduction.diagUnits a fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) k
  rw [Reduction.ideleModule_det_diagUnits_posIdele ρ hρ,
    Reduction.mem_normOneGL.1 (Reduction.maxCompact_le_normOneGL hk), mul_one] at hdet
  have hm := hmem
  simp only [band, Set.mem_setOf_eq, absDetA_eq] at hm
  rw [hdet] at hm
  obtain ⟨h1, h2⟩ := hm
  have hbb := hB b hb
  have hPd1 : P ^ d ≤ 2 / B₁ := by
    rw [le_div_iff₀ hB₁]
    calc P ^ d * B₁ ≤ P ^ d * (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
          mul_le_mul_of_nonneg_left hbb.1 (pow_nonneg hP.le _)
      _ = _ := mul_comm _ _
      _ ≤ 2 := h2
  have hPd2 : B₂⁻¹ ≤ P ^ d := by
    rw [inv_le_iff_one_le_mul₀' hB₂]
    calc (1 : ℝ) ≤ _ := h1
      _ ≤ B₂ * P ^ d := mul_le_mul_of_nonneg_right hbb.2 (pow_nonneg hP.le _)
  have hPlow : X₁ ≤ P := by
    rcases le_or_gt 1 P with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (hPd2.trans (pow_le_of_le_one hP.le h.le hd0.ne'))
  have hPup : P ≤ X₂ := by
    rcases le_or_gt P 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le hd0.ne').trans (hPd1.trans (le_max_right _ _))
  have hadj : ∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ Q * ρ j ∧ ρ j ≤ Q * ρ i := by
    intro i j hij
    constructor
    · exact (hup i j hij).trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (hρ j).le)
    · calc ρ j = t⁻¹ * (t * ρ j) := by field_simp
        _ ≤ t⁻¹ * ρ i := mul_le_mul_of_nonneg_left (hlow i j hij) (inv_nonneg.2 ht.le)
        _ ≤ Q * ρ i := mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_right _ _)) (hρ i).le
  have hratio := le_pow_mul_of_adjacent ρ hρ hQ hadj
  have hbox : ∀ i, ρ i ∈ Set.Icc lo hi := by
    intro i
    have ha0 : a ≠ 0 := by have := i.2; omega
    have hup' : ρ i ^ a ≤ Qa * P := by
      calc ρ i ^ a = ∏ _j : Fin a, ρ i := by simp
        _ ≤ ∏ j : Fin a, (Q ^ a * ρ j) :=
          Finset.prod_le_prod₀ (fun _ _ => (hρ i).le) fun j _ => hratio i j
        _ = Qa * P := by rw [Finset.prod_mul_distrib]; simp [hQadef, hPdef]
    have hlow' : P ≤ Qa * ρ i ^ a := by
      calc P = ∏ j : Fin a, ρ j := rfl
        _ ≤ ∏ _j : Fin a, (Q ^ a * ρ i) :=
          Finset.prod_le_prod₀ (fun j _ => (hρ j).le) fun j _ => hratio j i
        _ = Qa * ρ i ^ a := by rw [Finset.prod_mul_distrib]; simp [hQadef]
    constructor
    · rcases le_or_gt 1 (ρ i) with h | h
      · exact (min_le_left _ _).trans h
      · refine (min_le_right _ _).trans ?_
        refine (pow_le_of_le_one (hρ i).le h.le ha0).trans' ?_
        rw [div_le_iff₀ hQa, mul_comm]
        exact hPlow.trans hlow'
    · rcases le_or_gt (ρ i) 1 with h | h
      · exact h.trans (le_max_left _ _)
      · exact (le_self_pow₀ h.le ha0).trans (hup'.trans
          ((mul_le_mul_of_nonneg_left hPup hQa.le).trans (le_max_right _ _)))
  have hFρ : F ρ = Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) := by
    show Reduction.diagUnits a (h ρ) = _
    congr 1
    funext i
    exact posIdele_congr _ _ (max_eq_left (hbox i).1)
  rw [← hFρ]
  exact Set.mul_mem_mul (Set.mul_mem_mul hb ⟨ρ, fun i _ => hbox i, rfl⟩) hk

end GlobalTheory.SiegelBand
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompactDetBandSiegelSetStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCompact_detBand_siegelSet : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := by
  first | exact @GlobalTheory.SiegelBand.exists_isCompact_band_siegel | exact GlobalTheory.SiegelBand.exists_isCompact_band_siegel | (intros; apply GlobalTheory.SiegelBand.exists_isCompact_band_siegel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalNormLeOfOscillationScaledUnipFD
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalNormLeOfOscillationScaledUnipFD
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspTail

theorem norm_le_of_osc_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := by
  intro E _ _ _ a r hr hra φ _ hcusp hφ M hM x B hB
  set D := GroundTheory.Automorphic.scaledUnipFD E a r M with hDdef
  set ν := GroundTheory.Automorphic.AutomorphicForm.unipMeasure E a r
  have hD : IsAddFundamentalDomain (ratN E a r) D ν :=
    GroundTheory.Automorphic.isAddFundamentalDomain_scaledUnipFD hM
  have hD1 : ν D = 1 := GroundTheory.Automorphic.unipMeasure_scaledUnipFD hM
  have hunip : (unip : (BlockIx a r → Ad E) → GA E a) =
      (GroundTheory.Automorphic.AutomorphicForm.unipGL (n := a) (r := r) (R := Ad E)) :=
    funext fun X => Units.ext rfl
  have hcont : Continuous fun X : BlockIx a r → Ad E => φ (unip X * x) := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    rw [hunip]
    exact GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL
  obtain ⟨C, hC, hDC⟩ :=
    GroundTheory.Automorphic.CuspidalSpectrum.exists_isCompact_superset_scaledUnipFD (K := E) (n := a) r hM
  have hint : IntegrableOn (fun X => φ (unip X * x)) D ν :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hDC
  have hmean : ∫ X in D, φ (unip X * x) ∂ν = 0 :=
    hcusp r hr hra ν D inferInstance hD x
  have hfin : ν D < ⊤ := by rw [hD1]; exact ENNReal.one_lt_top
  have hkey : ∫ X in D, (φ (unip X * x) - φ x) ∂ν = -φ x := by
    rw [integral_sub hint (integrableOn_const hfin.ne)]
    simp only [hmean, setIntegral_const, measureReal_def, hD1, ENNReal.toReal_one, one_smul, zero_sub]
  calc ‖φ x‖ = ‖∫ X in D, (φ (unip X * x) - φ x) ∂ν‖ := by rw [hkey, norm_neg]
    _ ≤ B * ν.real D := norm_setIntegral_le_of_norm_le_const hfin hB
    _ = B := by simp [measureReal_def, hD1]

end GlobalTheory.CuspTail
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalNormLeOfOscillationScaledUnipFDStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_norm_le_of_oscillation_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := by
  first | exact @GlobalTheory.CuspTail.norm_le_of_osc_scaledUnipFD | exact GlobalTheory.CuspTail.norm_le_of_osc_scaledUnipFD | (intros; apply GlobalTheory.CuspTail.norm_le_of_osc_scaledUnipFD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsUniformlySmallOutsideCompactBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

noncomputable section
namespace GlobalTheory.HCF.Tail

theorem compactPart : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := GlobalTheory.T.exists_isCompact_detBand_siegelSet

theorem finConj : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := GlobalTheory.T.exists_conj_finiteUnipotent_mem_openSubgroup

theorem infConj : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (U : Set (GA E a)), U ∈ 𝓝 (1 : GA E a) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : GA E a) (P : BlockIx a r → Ad E), (∀ p, (P p).2 = 0) →
      ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a (((x⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) *
        GroundTheory.Automorphic.AutomorphicForm.blockEntry P * (x : Matrix (Fin a) (Fin a) (Ad E)))‖ ≤ δ →
      x⁻¹ * unip P * x ∈ U := GlobalTheory.T.conj_archUnipotent_mem_nhds_one

theorem meanZero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := GlobalTheory.T.cuspidal_norm_le_of_oscillation_scaledUnipFD

section Band
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem absDetA_mul (g h : GA E a) : absDetA (g * h) = absDetA g * absDetA h := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E),
    GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), map_mul, map_mul]
  rfl

theorem absDetA_ratGL (γ : GL (Fin a) E) : absDetA (ratGL E a γ) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (ratGL E a γ) = GroundTheory.Global.IdeleGroup.diagonal E (Matrix.GeneralLinearGroup.det γ) :=
    Units.ext (det_map _ γ)
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), h, GroundTheory.Global.IdeleGroup.ideleModule_diagonal]
  rfl

theorem absDetA_unip {r : ℕ} (P : BlockIx a r → Ad E) : absDetA (unip P) = 1 := by
  unfold absDetA
  rw [det_unip]
  simpa [absDetA] using (absDetA_one (E := E) (a := a))

theorem absDetA_conj (x u : GA E a) (hu : absDetA u = 1) : absDetA (x * (x⁻¹ * u * x)) = absDetA x := by
  have h1 : absDetA x⁻¹ * absDetA x = 1 := by rw [← absDetA_mul, inv_mul_cancel, absDetA_one]
  rw [absDetA_mul, absDetA_mul, absDetA_mul, hu, mul_one, h1, mul_one]

theorem mem_band_ratGL_mul {γ : GL (Fin a) E} {g : GA E a} (hg : g ∈ band E a) : ratGL E a γ * g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, absDetA_mul, absDetA_ratGL, one_mul] at hg ⊢
  exact hg

end Band

section Span
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {L : Subgroup (GL (Fin a) (Af E))}
  {W : Submodule ℂ (Kinf E a → ℂ)} {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ}

theorem span_left {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.1.left
  | zero => intro γ g; rfl
  | add x y _ _ hx hy => intro γ g; simp [hx γ g, hy γ g]
  | smul c x _ hx => intro γ g; simp [hx γ g]

theorem span_fin {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    ∀ l ∈ L, finRep E a l φ = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx.2.1
  | zero => intro l _; exact map_zero _
  | add x y _ _ hx hy => intro l hl; rw [map_add (f := _), hx l hl, hy l hl]
  | smul c x _ hx => intro l hl; rw [map_smul, hx l hl]

theorem span_right {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) {l : GL (Fin a) (Af E)} (hl : l ∈ L)
    (g : GA E a) : φ.1 (g * finGL E a l) = φ.1 g :=
  congrFun (congrArg Subtype.val (span_fin hφ l hl)) g

theorem span_cont (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) : Continuous φ.1 := by
  refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a φ ?_
  refine isOpen_iff_forall_mem_open.2 fun k hk => ⟨(fun l => k * l) '' (L : Set (GL (Fin a) (Af E))), ?_, ?_, ⟨1, L.one_mem, mul_one k⟩⟩
  · rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, span_fin hφ l hl]
    exact hk
  · exact (Homeomorph.mulLeft k).isOpenMap _ hL

end Span

open GroundTheory.Automorphic.Reduction in
theorem oneRoot (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (hX : X.Finite) (N : ℕ)
    {ω : Set (GA E a)} (hω : IsCompact ω) (hωB : ω ⊆ (adelicBorel (K := E) (n := a) : Set (GA E a)))
    {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 0 < r) (hra : r < a) :
    ∃ R : ℝ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ k ∈ (maxCompact (K := E) (n := a)),
      b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
      R * ρ ⟨r, hra⟩ ≤ ρ ⟨r - 1, by omega⟩ →
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k)‖ ≤ ε * M := by
  obtain ⟨U, hU, hequi⟩ := GlobalTheory.T.harishChandraForms_equicontinuous_on_band E a L hL W hW X hX N ε hε
  obtain ⟨M₀, hM₀, hfin⟩ := finConj E a r L hL ω hω
  obtain ⟨C₁, hC₁⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_norm_archMat_conj_le hω hωB ht hr hra
    (GroundTheory.Automorphic.isCompact_scaledInfSet (K := E) M₀)
  obtain ⟨δ, hδ, hinf⟩ := infConj E a r U hU
  refine ⟨max C₁ 0 / δ + 1, ?_⟩
  intro φ hφ hcusp M hM b hb ρ hρ hs k hk hband hR
  set x := b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k with hx
  have hq0 : 0 < ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩ := div_pos (hρ _) (hρ _)
  have hgain : C₁ * (ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩) ≤ δ := by
    set q := ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩
    set c := max C₁ 0
    have hc0 : 0 ≤ c := le_max_right _ _
    have hRq : (c / δ + 1) * q ≤ 1 := by
      rw [show q = ρ ⟨r, hra⟩ / ρ ⟨r - 1, by omega⟩ from rfl, mul_div_assoc', div_le_one (hρ _)]
      exact hR
    have h1 : C₁ * q ≤ c * q := mul_le_mul_of_nonneg_right (le_max_left _ _) hq0.le
    have h2 : c * q ≤ δ := by
      have e : c = δ * (c / δ) := by field_simp
      nlinarith [mul_nonneg (div_nonneg hc0 hδ.le) hq0.le]
    linarith
  refine meanZero E a r hr hra φ.1 (span_left hφ) hcusp (span_cont hL hφ) M₀ hM₀ x (ε * M) ?_
  intro Y hY
  have hsplit : unip Y * x = x * (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) * x) *
      (x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncFin Y) * x) := by
    conv_lhs => rw [← GroundTheory.Automorphic.CuspidalSpectrum.truncInf_add_truncFin Y, unip_add]
    group
  obtain ⟨l, hl, hle⟩ := hfin b hb ρ hρ k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncFin Y) (fun p => rfl)
    (fun p => GroundTheory.Automorphic.exists_finite_eq_natCast_mul hM₀ hY p)
  have hv : x⁻¹ * unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) * x ∈ U :=
    hinf x _ (fun p => rfl) ((hC₁ b hb ρ hρ hs k hk (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y) (fun p => rfl)
      (fun p => GroundTheory.Automorphic.infinite_mem_scaledInfSet hM₀ hY p)).trans hgain)
  rw [hsplit, hle, span_right hφ hl]
  refine hequi φ hφ M hM x hband _ hv ?_
  have h := absDetA_conj x (unip (GroundTheory.Automorphic.CuspidalSpectrum.truncInf Y)) (absDetA_unip _)
  simp only [band, Set.mem_setOf_eq] at hband ⊢
  rw [h]
  exact hband


open GroundTheory.Automorphic.Reduction in
theorem tails : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W →
    ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : Set (GA E a), IsCompact C ∧
    C ⊆ band E a ∧ ∀ g ∈ band E a, (∃ γ : GL (Fin a) E, ratGL E a γ * g ∈ C) ∨
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ‖φ.1 g‖ ≤ ε * M := by
  intro E _ _ _ a L hL W hW X hX N ε hε
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) a
  have hex : ∀ r : ℕ, ∀ (hr : 0 < r) (hra : r < a), ∃ R : ℝ, _ := fun r hr hra =>
    oneRoot E a L hL W hW X hX N hω hωB ht hε hr hra
  choose Rf hRf using hex
  set R : ℝ := 1 + ∑ r : Fin a, if h : 0 < (r : ℕ) then max (Rf r h r.2) 0 else 0 with hRdef
  have hRle : ∀ (r : ℕ) (hr : 0 < r) (hra : r < a), Rf r hr hra ≤ R := by
    intro r hr hra
    have h1 := Finset.single_le_sum (f := fun r : Fin a => if h : 0 < (r : ℕ) then max (Rf r h r.2) 0 else 0)
      (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hra⟩)
    simp only [hr, dif_pos] at h1
    linarith [le_max_left (Rf r hr hra) 0]
  obtain ⟨C, hC, hCb, hCmem⟩ := compactPart E a ω hω t R ht
  refine ⟨C, hC, hCb, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg g
  obtain ⟨b, hb, _, ⟨ρ, hρ, hs, rfl⟩, k, hk, he⟩ := hγ
  have he' : ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * k := he
  have hgb : ratGL E a γ * g ∈ band E a := mem_band_ratGL_mul hg
  by_cases hall : ∀ (r : ℕ) (hr : 0 < r) (hra : r < a), ρ ⟨r - 1, by omega⟩ ≤ R * ρ ⟨r, hra⟩
  · refine Or.inl ⟨γ, ?_⟩
    rw [he'] at hgb ⊢
    refine hCmem b hb ρ hρ hs (fun i j hij => ?_) k hk hgb
    have h1 := hall j (by omega) j.2
    have e : (⟨(j : ℕ) - 1, by omega⟩ : Fin a) = i := Fin.ext (by simp; omega)
    rwa [e] at h1
  · push_neg at hall
    obtain ⟨r, hr, hra, hlt⟩ := hall
    refine Or.inr fun φ hφ hc M hM => ?_
    rw [← span_left hφ γ g, he']
    rw [he'] at hgb
    refine hRf r hr hra φ hφ hc M hM b hb ρ hρ hs k hk hgb ?_
    exact (mul_le_mul_of_nonneg_right (hRle r hr hra) (hρ _).le).trans hlt.le

end GlobalTheory.HCF.Tail

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsUniformlySmallOutsideCompactBandStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_uniformly_small_outside_compact_band : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧ ∀ g ∈ band E a, (∃ γ : GL (Fin a) E, ratGL E a γ * g ∈ C) ∨ ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) → ‖φ.1 g‖ ≤ ε * M := by
  first | exact @GlobalTheory.HCF.Tail.tails | exact GlobalTheory.HCF.Tail.tails | (intros; apply GlobalTheory.HCF.Tail.tails <;> assumption)
end
