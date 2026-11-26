module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualComapOrthonormalFrameUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualComapOrthonormalFrameUnimodular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePull

theorem unimod_comap_frame : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).Unimod := by
  intro D V fr Λ hG hΛ v
  have hstar : ∀ x : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = x) → ∃ b : 𝓞 D.host.E, (b : D.host.E) = star x := by
    rintro x ⟨b, rfl⟩
    exact ⟨Formalism.L2.Pj.barE D b, Formalism.L2.Pj.barE_eq_star D b⟩
  have hcT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 = fr.1ᴴ := by
    ext i j
    rfl
  have key : ∀ w : Fin V.rank → D.host.E,
      ∑ i, ∑ j, star ((fr.1 *ᵥ w) i) * V.gram i j * (fr.1 *ᵥ v) j = ∑ j, star (w j) * v j := by
    intro w
    have e1 : ∀ x y : Fin V.rank → D.host.E,
        ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y) := by
      intro x y
      simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
      rfl
    rw [e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← hcT, hG, Matrix.one_mulVec]
    rfl
  have hsum : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (w j) * v j) = ∑ j, star (v j) * w j := by
    intro w
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hsum' : ∀ w : Fin V.rank → D.host.E, star (∑ j, star (v j) * w j) = ∑ j, star (w j) * v j := by
    intro w
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_star, mul_comm]
  change fr.1 *ᵥ v ∈ Λ ↔ ∀ w, fr.1 *ᵥ w ∈ Λ → ∃ b : 𝓞 D.host.E, (b : D.host.E) = ∑ j, star (v j) * w j
  rw [hΛ.2]
  constructor
  · intro H w hw
    have := hstar _ (H _ hw)
    rwa [key, hsum] at this
  · intro H x hx
    have hw : fr.1 *ᵥ ((fr⁻¹).1 *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := hstar _ (H ((fr⁻¹).1 *ᵥ x) (by rw [hw]; exact hx))
    rw [hsum', ← key, hw] at this
    exact this

end GlobalTheory.FramePull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualComapOrthonormalFrameUnimodularStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_comap_orthonormalFrame_unimodular : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).Unimod := by
  first | exact @GlobalTheory.FramePull.unimod_comap_frame | exact GlobalTheory.FramePull.unimod_comap_frame | (intros; apply GlobalTheory.FramePull.unimod_comap_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryAdelicMatrixConjOrthonormalFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryAdelicMatrixConjOrthonormalFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitConjFrame

open GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem sg_one_tmul (c : E ≃ₐ[F] E) (e : E) :
    sg (FiniteAdeleRing (𝓞 F) F) c ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] e) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c e := by
  simp [sg, Algebra.TensorProduct.map_tmul]

theorem fm_map_sg (c : E ≃ₐ[F] E) (A : Matrix (Fin n) (Fin n) E) :
    (fm F A).map (sg (FiniteAdeleRing (𝓞 F) F) c) = fm F (A.map c) := by
  ext i j
  simp only [fm, Matrix.map_apply, sg_one_tmul]

theorem hermA_eq_dot (c : E ≃ₐ[F] E) (H : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c H x y = x ⬝ᵥ (fm F H *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
  simp only [hermA, dotProduct, Matrix.mulVec, fm, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hermA_mulVec (c : E ≃ₐ[F] E) (H : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (RA F E))
    (x y : Fin n → RA F E) :
    hermA c H (M *ᵥ x) (M *ᵥ y) =
      x ⬝ᵥ ((Mᵀ * fm F H * M.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ
        fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
  rw [hermA_eq_dot]
  have h1 : (fun b => sg (FiniteAdeleRing (𝓞 F) F) c ((M *ᵥ y) b)) =
      M.map (sg (FiniteAdeleRing (𝓞 F) F) c) *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b) := by
    funext b
    exact RingHom.map_mulVec (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom M y b
  rw [h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem sg_single (c : E ≃ₐ[F] E) (j : Fin n) :
    (fun b => sg (FiniteAdeleRing (𝓞 F) F) c ((Pi.single j (1 : RA F E) : Fin n → RA F E) b)) = Pi.single j 1 := by
  funext b
  by_cases h : b = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem mat_eq_of_dot (c : E ≃ₐ[F] E) {K K' : Matrix (Fin n) (Fin n) (RA F E)}
    (h : ∀ x y : Fin n → RA F E, x ⬝ᵥ (K *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) =
      x ⬝ᵥ (K' *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b))) : K = K' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [sg_single] at this
  simpa [Matrix.mulVec_single_one] using this

theorem gram_of_isUnA (c : E ≃ₐ[F] E) {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c 1 g) :
    gᵀ * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) = 1 := by
  have h := mat_eq_of_dot c (K := gᵀ * fm F 1 * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) (K' := fm F 1)
    fun x y => by rw [← hermA_mulVec, ← hermA_eq_dot]; exact hg x y
  rwa [GlobalTheory.UnRep.FullReps.fm_one, Matrix.mul_one] at h

end General

end GlobalTheory.UnitConjFrame

namespace GlobalTheory.UnitConjFrame

open GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem map_mul_sg (c : E ≃ₐ[F] E) (M N : Matrix (Fin n) (Fin n) (RA F E)) :
    (M * N).map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      M.map (sg (FiniteAdeleRing (𝓞 F) F) c) * N.map (sg (FiniteAdeleRing (𝓞 F) F) c) :=
  Matrix.map_mul (f := (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom)

theorem map_mul_c (c : E ≃ₐ[F] E) (M N : Matrix (Fin n) (Fin n) E) :
    (M * N).map c = M.map c * N.map c :=
  Matrix.map_mul (f := (c : E →+* E))

theorem fm_transpose (A : Matrix (Fin n) (Fin n) E) : (fm F A)ᵀ = fm F Aᵀ := by
  ext i j; rfl

theorem isUnA_conj (c : E ≃ₐ[F] E) (A B G : Matrix (Fin n) (Fin n) E) (hAB : A * B = 1)
    (h : Aᵀ * Gᵀ * A.map c = 1) {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c 1 g) :
    IsUnA c Gᵀ (fm F A * g * fm F B) := by
  have hg' := gram_of_isUnA c hg
  have hB : Bᵀ * B.map c = Gᵀ := by
    have e1 : Bᵀ * B.map c = Bᵀ * (Aᵀ * Gᵀ * A.map c) * B.map c := by rw [h, Matrix.mul_one]
    rw [e1, ← Matrix.transpose_transpose Gᵀ]
    have e2 : (A * B).map c = A.map c * B.map c := map_mul_c c A B
    rw [hAB, Matrix.map_one _ (map_zero c) (map_one c)] at e2
    calc Bᵀ * (Aᵀ * Gᵀᵀᵀ * A.map c) * B.map c = (A * B)ᵀ * Gᵀᵀᵀ * (A.map c * B.map c) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Gᵀᵀᵀ := by rw [hAB, ← e2, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hM : (fm F A * g * fm F B)ᵀ * fm F Gᵀ * (fm F A * g * fm F B).map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      fm F Gᵀ := by
    rw [map_mul_sg, map_mul_sg, fm_map_sg, fm_map_sg, Matrix.transpose_mul, Matrix.transpose_mul,
      fm_transpose, fm_transpose]
    have e3 : fm F Aᵀ * fm F Gᵀ * fm F (A.map c) = 1 := by
      rw [← GlobalTheory.UnRep.FullReps.fm_mul, ← GlobalTheory.UnRep.FullReps.fm_mul, h, GlobalTheory.UnRep.FullReps.fm_one]
    calc _ = fm F Bᵀ * (gᵀ * (fm F Aᵀ * fm F Gᵀ * fm F (A.map c)) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *
            fm F (B.map c) := by simp only [Matrix.mul_assoc]
      _ = fm F Gᵀ := by
          rw [e3, Matrix.mul_one, hg', Matrix.mul_one, ← GlobalTheory.UnRep.FullReps.fm_mul, hB]
  intro x y
  rw [hermA_mulVec, hM, hermA_eq_dot]

end General

end GlobalTheory.UnitConjFrame

theorem GlobalTheory.UnitConjFrame.isUnA_frame_conj : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g →
    GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) V.gramᵀ (GlobalTheory.UnRep.fm D.host.F fr.1 * g * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1) := by
  intro D V fr g hfr hg
  refine GlobalTheory.UnitConjFrame.isUnA_conj (GlobalTheory.Member.cF D) fr.1 (fr⁻¹).1 V.gram (Units.mul_inv fr) ?_ hg
  have h := congrArg Matrix.transpose hfr
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_one] at h
  rw [← h, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.mul_assoc]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryAdelicMatrixConjOrthonormalFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitaryAdelicMatrix_conj_orthonormalFrame : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g →
    GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) V.gramᵀ (GlobalTheory.UnRep.fm D.host.F fr.1 * g * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1) := by
  first | exact @GlobalTheory.UnitConjFrame.isUnA_frame_conj | exact GlobalTheory.UnitConjFrame.isUnA_frame_conj | (intros; apply GlobalTheory.UnitConjFrame.isUnA_frame_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenusTranslate

open GlobalTheory.AdLat GlobalTheory.UnRep

theorem hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    z ∈ Formalism.L2.Herm.hatL L ↔
      (fun i => (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm (z i)) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  refine ⟨GlobalTheory.PrincInLevel.swap_symm_mem_hat L z, fun h => ?_⟩
  have := GlobalTheory.PrincInLevel.swap_mem_hatL L _ h
  simpa using this


set_option maxHeartbeats 2000000 in
theorem exists_move_colLat : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    ∃ x : GA D V, x ∈ GfC V ∧ ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (Formalism.IndefR.Lev.finE V x).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  intro D V fr Λ hfr hΛ
  have hU := GlobalTheory.T.selfDual_comap_orthonormalFrame_unimodular D V fr Λ hfr hΛ
  have hT : (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).TrivAt 1 :=
    ⟨0, Nat.coprime_zero_left 1 |>.2 rfl, by simp, by simp⟩
  have hgen : ∃ g : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E), GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g.1 ∧
      ∀ z, z ∈ GlobalTheory.AdLat.hat D.host.F ((Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔
      (g⁻¹).1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) := by
    obtain ⟨g, hgU, hgL, -⟩ := GlobalTheory.AdelTranslate.exists_adelic_translate D.host.E (Formalism.L2.Pj.hostOfRecord D) V.rank 1 _
      one_pos hU hT
    have hstd := GlobalTheory.UnRep.StdInhab.main D.host.E (Formalism.L2.Pj.hostOfRecord D) V.rank
    have hfg := hstd.2.2.1
    have hsp := hstd.2.2.2.1
    have hL := GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield D.host.E) D.host.E V.rank
      (Formalism.L2.Pj.stdLat D.host.E V.rank) g hfg hsp
    obtain ⟨Λ'', hL''⟩ := hL
    have h1 := hL''.1
    have h4 := hL''.2.2.2
    have e : Λ'' = Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)) :=
      SetLike.coe_injective (h1.trans hgL.symm)
    refine ⟨g, by
      have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
      rw [hc]; exact hgU, fun z => ?_⟩
    rw [← e, ← SetLike.mem_coe, h4]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · intro hz
      exact ⟨_, hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  obtain ⟨g, hgU, hg'⟩ := hgen
  have hfm1 : GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 * GlobalTheory.UnRep.fm D.host.F fr.1 = 1 := by
    rw [← GlobalTheory.UnRep.FullReps.fm_mul, Units.inv_mul, GlobalTheory.UnRep.FullReps.fm_one]
  have hfm2 : GlobalTheory.UnRep.fm D.host.F fr.1 * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 = 1 := by
    rw [← GlobalTheory.UnRep.FullReps.fm_mul, Units.mul_inv, GlobalTheory.UnRep.FullReps.fm_one]
  obtain ⟨U, hU1, hU2⟩ : ∃ U : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E),
      U.1 = GlobalTheory.UnRep.fm D.host.F fr.1 ∧ (U⁻¹).1 = GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 :=
    ⟨⟨GlobalTheory.UnRep.fm D.host.F fr.1, GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1, hfm2, hfm1⟩, rfl, rfl⟩
  have hX := GlobalTheory.T.isUnitaryAdelicMatrix_conj_orthonormalFrame D V fr g.1 hfr hgU
  rw [← hU1, ← hU2, ← Units.val_mul, ← Units.val_mul] at hX
  obtain ⟨X, hXe⟩ : ∃ X : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E), X = U * g * U⁻¹ := ⟨_, rfl⟩
  rw [← hXe] at hX
  have hlift := (GlobalTheory.UnitarySplit.real_finite_split D V).2.2.2.1 X hX
  obtain ⟨x, hx, hxX⟩ := hlift
  have key : ∀ w : Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E,
      w ∈ GlobalTheory.AdLat.hat D.host.F (colLat fr : Set (Fin V.rank → D.host.E)) ↔
        X.1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    intro w
    have ew : GlobalTheory.UnRep.fm D.host.F fr.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← GlobalTheory.UnRep.FullReps.fm_mul, Units.mul_inv, GlobalTheory.UnRep.FullReps.fm_one, Matrix.one_mulVec]
    have h1 := GlobalTheory.T.adelicCompletion_comap_rational_matrix D.host.F D.host.E V.rank fr (colLat fr) (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w)
    rw [ew, GlobalTheory.T.columnLattice_comap_eq_standardLattice] at h1
    have h2 := GlobalTheory.T.adelicCompletion_comap_rational_matrix D.host.F D.host.E V.rank fr Λ (g.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w))
    have hgg : (g⁻¹).1 *ᵥ (g.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w)) = GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hg', hgg] at h2
    rw [h1, hXe, Units.val_mul, Units.val_mul, hU1, hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]
  refine ⟨x, hx, fun v => ?_⟩
  have hfin : (fun i => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm
      (((Formalism.IndefR.Lev.finE V x).1 *ᵥ v) i)) =
      X.1 *ᵥ fun i => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v i) := by
    have hfe : Formalism.IndefR.Lev.finE V x = Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) X := by rw [← hxX]; rfl
    rw [hfe]
    funext i
    rw [AlgEquiv.symm_apply_eq]
    have hv : ⇑(Formalism.IndefR.Lev.swapAE D) ∘ (fun j =>
        (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v j)) = v :=
      funext fun j => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).apply_symm_apply (v j)
    have hm := RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) X.1
      (fun j => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v j)) i
    rw [hv] at hm
    exact hm.symm
  rw [hatL_iff, hatL_iff, hfin]
  exact key _

end GlobalTheory.GenusTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitary_moves_selfDualLattice : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    ∃ x : GA D V, x ∈ GfC V ∧ ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (Formalism.IndefR.Lev.finE V x).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  first | exact @GlobalTheory.GenusTranslate.exists_move_colLat | exact GlobalTheory.GenusTranslate.exists_move_colLat | (intros; apply GlobalTheory.GenusTranslate.exists_move_colLat <;> assumption)
end
