module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicRationalCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameReduceRank
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryHeightBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryLowerBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawa
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawa
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW
  obtain ⟨K₁, h₁, c₁, iw₁, lev⟩ := GlobalTheory.CompanionTheory.SiegelArch.exists_kInf F E σ hcm n J hJ r X Y hW
  obtain ⟨K₂, h₂, c₂, iw₂, good⟩ := GlobalTheory.T.unitary_adelic_iwasawa_compact F E σ hcm n J hJ r X Y hW
  obtain ⟨K, hK, iw, -⟩ := GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa F E σ hcm n J hJ r X Y hW
    K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ lev good
  exact ⟨K, hK, iw⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame | exact GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicScalesIsotropic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicScalesIsotropic
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov

theorem exists_sends_of_rat_mem_minPar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
    ∀ δ ∈ ratPts σ J, δ ∈ minPar σ J X → ∃ e : E, e ≠ 0 ∧ Sends σ J δ (e • Xᵀ 0) (Xᵀ 0) := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW δ hδ hp
  have hF := pfrA hcm hJ hW
  have hinc : Function.Injective (inclR (F := F) (E := E) (AF F)) := fun a b h =>
    congrFun (ratV_injective (F := F) (n := 1) (a₁ := fun _ => a) (a₂ := fun _ => b) (funext fun _ => h)) 0
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin n) E,
      (matHom _ σ J δ).1 = (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (show (((show ↥(HR (AF F) σ J) from δ) : HR (AF F) σ J) :
      GL (Fin n) (AF F ⊗[F] E)) ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) from hδ)
    exact ⟨g, (congrArg Units.val hg).symm⟩
  set Bq : Matrix (Fin (r + 1)) (Fin (r + 1)) E := cT (σ : E →+* E) Y * J * ((g : Matrix (Fin n) (Fin n) E) * X) with hBq
  have hBm : Bm σ J X Y δ = Bq.map (inclR (F := F) (AF F)) := by
    unfold Bm coefM JR
    rw [hg, hBq, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, cT_map_inclR]
  obtain ⟨hbt, he⟩ := (mem_minPar_iff hF).1 hp
  rw [hBm] at hbt he
  have hgX : (g : Matrix (Fin n) (Fin n) E) * X = X * Bq := by
    apply Matrix.map_injective hinc
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, ← hg]
    exact he
  have hlow : ∀ k : Fin (r + 1), k ≠ 0 → Bq k 0 = 0 := fun k hk => by
    apply hinc
    have := hbt (show id (0 : Fin (r + 1)) < id k from Fin.pos_of_ne_zero hk)
    simpa using this
  have hcol : (g : Matrix (Fin n) (Fin n) E) *ᵥ Xᵀ 0 = Bq 0 0 • Xᵀ 0 := by
    funext i
    have h1 := congrFun (congrFun hgX i) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (r + 1))
      (fun k _ hk => by rw [hlow k hk, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)] at h1
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h1
  have hx : Xᵀ 0 ≠ 0 := fun h0 => by
    have h1 := congrFun (congrFun hW.xy 0) 0
    rw [GlobalTheory.SiegelSet.gram_apply, h0, map_zero, LinearMap.zero_apply, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  have hb : Bq 0 0 ≠ 0 := fun h0 => hx (by
    rw [h0, zero_smul] at hcol
    have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v) hcol
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h2)
  refine ⟨(Bq 0 0)⁻¹, inv_ne_zero hb, ?_⟩
  have h3 : (g : Matrix (Fin n) (Fin n) E) *ᵥ ((Bq 0 0)⁻¹ • Xᵀ 0) = Xᵀ 0 := by
    rw [Matrix.mulVec_smul, hcol, smul_smul, inv_mul_cancel₀ hb, one_smul]
  unfold Sends
  rw [hg]
  funext i
  have h4 := RingHom.map_mulVec (inclR (F := F) (E := E) (AF F)) (g : Matrix (Fin n) (Fin n) E) ((Bq 0 0)⁻¹ • Xᵀ 0) i
  rw [h3] at h4
  exact h4.symm

end GlobalTheory.CompanionTheory.RedCov

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicScalesIsotropicStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_scales_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ δ ∈ ratPts σ J, δ ∈ minPar σ J X → ∃ e : E, e ≠ 0 ∧ Sends σ J δ (e • Xᵀ 0) (Xᵀ 0) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar | exact GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitarySendsIsotropic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitarySendsIsotropic
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov


open GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume Module in
theorem exists_ratPts_sends_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ v : Fin n → E, v ≠ 0 → hE σ J v v = 0 → ∃ γ ∈ ratPts σ J, Sends σ J γ (Xᵀ 0) v := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW v hv hvv
  obtain ⟨hF, hEc, h2, hc⟩ := hσ
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  have hH : IsHermitianFor (conjHom F E) J := Matrix.ext fun i j => hJ.1 i j
  obtain ⟨h, hg, hform⟩ : ∃ h : HermitianForm F E (Fin n → E), gram h.toSesq (Pi.basisFun E (Fin n)) = J ∧
      ∀ x y, h.toSesq x y = hE (conj F E).toAlgHom J x y :=
    ⟨HermitianForm.ofGram J hH hu, gram_ofGram J hH hu, fun x y => rfl⟩
  have key : ∀ A B : Matrix (Fin n) (Fin (r + 1)) E, h.toSesq (Aᵀ 0) (Bᵀ 0) =
      (cT (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) A * J * B) 0 0 := by
    intro A B
    rw [hform]
    simp only [hE, Formalism.UG.hform, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hxx : h.toSesq (Xᵀ 0) (Xᵀ 0) = 0 := by rw [key, hW.xx]; rfl
  have hyy : h.toSesq (Yᵀ 0) (Yᵀ 0) = 0 := by rw [key, hW.yy]; rfl
  have hxy : h.toSesq (Xᵀ 0) (Yᵀ 0) = 1 := by rw [key, hW.xy]; simp
  obtain ⟨w, hvw, hww⟩ := WittPartner.full h v hv (by rw [hform]; exact hvv)
  obtain ⟨g, hgv, -⟩ := HyperbolicPairTransitive.full h (Xᵀ 0) (Yᵀ 0) v w ⟨hxx, hyy, hxy⟩
    ⟨by rw [hform]; exact hvv, hww, hvw⟩
  obtain ⟨M, hM, hact⟩ : ∃ M : GL (Fin n) E, M ∈ Formalism.UG.UJ (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) J ∧
      (M : Matrix (Fin n) (Fin n) E) *ᵥ (Xᵀ 0) = v := by
    have h3 : ∀ N : GL (Fin n) E, N ∈ unitaryGroupMatrix (conjHom F E) (gram h.toSesq (Pi.basisFun E (Fin n))) →
        N ∈ Formalism.UG.UJ (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) J := by
      rw [hg]
      exact fun N hN => hN
    refine ⟨_, h3 _ (unitaryGroupEquivMatrix h (Pi.basisFun E (Fin n)) g).2, ?_⟩
    rw [unitaryGroupEquivMatrix_apply, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_mulVec]
    exact hgv
  refine ⟨ratEmb _ J ⟨M, hM⟩, by rw [← range_ratEmb]; exact ⟨_, rfl⟩, ?_⟩
  unfold Sends
  funext i
  rw [← hact]
  have e : (matHom _ _ J (ratEmb _ J ⟨M, hM⟩)).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := rfl
  rw [e]
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ _ i).symm

end GlobalTheory.CompanionTheory.RedCov

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitarySendsIsotropicStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_sends_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ v : Fin n → E, v ≠ 0 → hE σ J v v = 0 → ∃ γ ∈ ratPts σ J, Sends σ J γ (Xᵀ 0) v := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_ratPts_sends_isotropic | exact GlobalTheory.CompanionTheory.RedCov.exists_ratPts_sends_isotropic | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_ratPts_sends_isotropic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitaryWittExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitaryWittExtension
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

theorem hE_mulVec_self {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J M : Matrix (Fin n) (Fin n) E) (hM : cT (σ : E →+* E) M * J * M = J) (w : Fin n → E) :
    hE σ J (M *ᵥ w) (M *ᵥ w) = hE σ J w w := by
  have key : ∀ x y : Fin n → E, hE σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]
  have hs : (fun i => σ ((M *ᵥ w) i)) = (M.map (σ : E →+* E)) *ᵥ (fun i => σ (w i)) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) M w i
  rw [key, key, hs, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  have : (M.map (σ : E →+* E))ᵀ *ᵥ ((J * M) *ᵥ w) = J *ᵥ w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    have h := hM
    unfold cT at h
    rw [h]
  rw [this]

theorem exists_sends_hE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w := by
  intro F E _ _ _ _ _ σ _ n J _ γ hγ w
  obtain ⟨M, hM, e⟩ := hγ
  refine ⟨(M : Matrix (Fin n) (Fin n) E) *ᵥ w, ?_, hE_mulVec_self σ J _ hM w⟩
  have e' : (matHom _ σ J γ).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    have := congrArg (fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) e
    exact this.symm
  unfold Sends
  rw [e']
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (M : Matrix (Fin n) (Fin n) E) w i).symm

end GlobalTheory.CompanionTheory.RedCov

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitaryWittExtensionStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_witt_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_sends_hE | exact GlobalTheory.CompanionTheory.RedCov.exists_sends_hE | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_sends_hE <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNearMinimalVector
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNearMinimalVector
noncomputable section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic GroundTheory.Automorphic.Reduction

section NearMin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ}

def ratCoords [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F :=
  resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i))

theorem hv_eq_adelicNorm_resVec [Algebra.IsQuadraticExtension F E] (ξ : Fin n → AF F ⊗[F] E) :
    hv (F := F) (E := E) ξ = adelicNorm (resVec (Module.finBasis F E) (AF F) ξ) := rfl

theorem ratCoords_ne_zero [Algebra.IsQuadraticExtension F E] {u : Fin n → E} (hu : u ≠ 0) :
    ratCoords (F := F) u ≠ 0 := by
  intro h0
  apply hu
  have h1 : (fun i => inclR (F := F) F (u i)) = fun _ : Fin n => (0 : F ⊗[F] E) := by
    apply resVec_injective (Module.finBasis F E) F
    rw [show resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i)) = 0 from h0]
    funext p
    simp [resVec, coordsVec]
  funext i
  have h2 := congrFun h1 i
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective
    (h2.trans (map_zero _).symm)

theorem resVec_ratV [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    resVec (Module.finBasis F E) (AF F) (ratV F u) = ratVec (ratCoords (F := F) u) := by
  have h := resVec_baseMap (Module.finBasis F E) (Algebra.ofId F (AF F))
    (fun i => inclR (F := F) F (u i))
  have e : (fun i => baseMap (Algebra.ofId F (AF F)) (inclR (F := F) F (u i))) = ratV F u := by
    funext i
    simp [ratV, inclR, baseMap]
  rw [e] at h
  rw [h]
  rfl

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem exists_pos_le_hgt [Algebra.IsQuadraticExtension F E] (g : GAd σ J) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Fin n → E, u ≠ 0 → c ≤ hgt σ J g u := by
  set T := trHom (Module.finBasis F E) (AF F) (matHom _ σ J g) with hT
  obtain ⟨P, hP, h⟩ := exists_adelicNorm_vecMul_le_mul (K := F) (C := {T⁻¹}) isCompact_singleton
  refine ⟨1 / P, one_div_pos.2 hP, fun u hu => ?_⟩
  have hx := ratCoords_ne_zero (F := F) hu
  have e2 : hgt σ J g u = adelicNorm (ratVec (ratCoords (F := F) u) ᵥ* (T : Matrix (Fin (Fintype.card (Fin n × Fin (Module.finrank F E))))
      (Fin (Fintype.card (Fin n × Fin (Module.finrank F E)))) (AF F))) := by
    rw [hT, ← resVec_ratV, resVec_vecMul_trHom, ← hv_eq_adelicNorm_resVec, hgt, map_inv]
  have h3 := h T⁻¹ rfl _ ((hasFiniteContent_ratVec hx).vecMul T)
  rw [← e2, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one] at h3
  rw [div_le_iff₀ hP, mul_comm]
  exact (one_le_adelicNorm_ratVec hx).trans h3

end NearMin

theorem exists_isotropic_of_isWittFrame {F E : Type} [Field F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} (h : IsWittFrame σ J X Y) :
    ∃ v : Fin n → E, v ≠ 0 ∧ hE σ J v v = 0 := by
  refine ⟨Xᵀ 0, fun h0 => ?_, ?_⟩
  · have h1 := congrFun (congrFun h.xy 0) 0
    have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
    simp [cT, Matrix.mul_apply, hc] at h1
  · have h1 := congrFun (congrFun h.xx 0) 0
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Matrix.zero_apply] at h1
    rw [Finset.sum_comm] at h1
    simpa [hE, Formalism.UG.hform] using h1

theorem exists_nearMin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ g : GAd σ J, ∃ v, NearMin σ J g v := by
  intro F E _ _ _ _ _ σ hCM n J _ r X Y hW g
  haveI : Algebra.IsQuadraticExtension F E := ⟨hCM.2.2.1⟩
  obtain ⟨c, hc, hlow⟩ := exists_pos_le_hgt σ J g
  obtain ⟨v₀, hv₀, hi₀⟩ := exists_isotropic_of_isWittFrame hW
  let S : Set ℝ := {t | ∃ u : Fin n → E, u ≠ 0 ∧ hE σ J u u = 0 ∧ t = hgt σ J g u}
  have hne : S.Nonempty := ⟨_, v₀, hv₀, hi₀, rfl⟩
  have hbdd : BddBelow S := ⟨c, by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu⟩
  have hm : c ≤ sInf S := le_csInf hne (by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu)
  have hm0 : 0 < sInf S := hc.trans_le hm
  obtain ⟨_, ⟨v, hv, hi, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (show sInf S < 2 * sInf S by linarith)
  refine ⟨v, hv, hi, fun u hu hiu => ?_⟩
  have : sInf S ≤ hgt σ J g u := csInf_le hbdd ⟨u, hu, hiu, rfl⟩
  linarith

end GlobalTheory.CompanionTheory.RedCov

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNearMinimalVectorStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_near_minimal_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ g : GAd σ J, ∃ v, NearMin σ J g v := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_nearMin | exact GlobalTheory.CompanionTheory.RedCov.exists_nearMin | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_nearMin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySiegelDomainExists
set_option linter.unusedSectionVars false
noncomputable section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

open GlobalTheory.CompanionTheory.RedCov

namespace GlobalTheory.CompanionTheory.RedCov

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem torus_zero {X Y : Matrix (Fin n) (Fin r) E} {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) : a 0 = 1 := by
  have := ha.add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem mul_mem_one (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y)
    {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {p q : GAd σ J} (hp : p ∈ minParOne σ J X)
    (hq : q ∈ minParOne σ J X) : p * q ∈ minParOne σ J X := by
  obtain ⟨τ, -, h2, -, h4, h5⟩ := exists_tau h hJ hW ha
  have hp' := minParOne_subset hp
  have hq' := minParOne_subset hq
  have e := h2 ⟨p, hp'⟩ ⟨q, hq'⟩
  rw [h4 p hp, h4 q hq, add_zero] at e
  have := h5 (⟨p, hp'⟩ * ⟨q, hq'⟩)
  rw [e, torus_zero ha, inv_one, mul_one] at this
  exact this

theorem ratV_zero : ratV F (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

theorem nearMin_rat (hact : ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w)
    {g γ : GAd σ J} {u v : Fin n → E} (hN : NearMin σ J g v) (hγ : γ ∈ ratPts σ J)
    (hs : Sends σ J γ u v) : NearMin σ J (γ⁻¹ * g) u := by
  have hz : ∀ {w w' : Fin n → E}, Sends σ J γ w w' → w ≠ 0 → w' ≠ 0 := by
    intro w w' hs' hw e
    apply hw
    have h1 := hs'.inv
    unfold Sends at h1
    rw [e, ratV_zero, Matrix.mulVec_zero] at h1
    exact ratV_injective (h1.symm.trans ratV_zero.symm)
  obtain ⟨v', hv', hvv⟩ := hact γ hγ u
  have e : v' = v := ratV_injective (hv'.symm.trans hs)
  subst e
  refine ⟨?_, ?_, ?_⟩
  · intro hu
    subst hu
    apply hN.1
    unfold Sends at hs
    rw [ratV_zero, Matrix.mulVec_zero] at hs
    exact ratV_injective (hs.symm.trans ratV_zero.symm)
  · rw [← hvv]; exact hN.2.1
  · intro w hw hww
    obtain ⟨w', hw', hww'⟩ := hact γ hγ w
    rw [hgt_mul hs.inv, hgt_mul hw'.inv]
    exact hN.2.2 w' (hz hw' hw) (hww'.trans hww)

theorem step {r : ℕ} (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y)
    (IH : ∀ (n' : ℕ) (J' : Matrix (Fin n') (Fin n') E) (X' Y' : Matrix (Fin n') (Fin r) E),
      IsHermND σ J' → IsWittFrame σ J' X' Y' → HasRed σ J' X' Y') : HasRed σ J X Y := by
  intro a ha
  obtain ⟨K, hKc, hIw⟩ := GlobalTheory.T.unitary_adelic_iwasawa F E σ h n J hJ (r + 1) X Y hW
  obtain ⟨n', J', X', Y', ι, hJ', hW', hιc, hιr, hιx, hι1, hιa⟩ := GlobalTheory.T.witt_frame_reduce_rank F E σ h n J hJ r X Y hW
  obtain ⟨hιt, hιcomm, hιdec⟩ := hιa a ha
  obtain ⟨a', ha'⟩ := exists_isTorus h hJ' hW'
  obtain ⟨C', c', hC', hc', hred'⟩ := IH n' J' X' Y' hJ' hW' a' ha'
  obtain ⟨Ω, hΩc, hΩ1, hΩ⟩ := GlobalTheory.T.minimal_parabolic_rational_compact F E σ h n J hJ (r + 1) X Y hW
  have hC₁ : IsCompact ((ι '' C') * (K : Set (GAd σ J))) := (hC'.image hιc).mul hKc
  obtain ⟨M₁, hM₁, hfirst⟩ := GlobalTheory.T.reduction_theory_height_bound F E σ h n J hJ r X Y hW a ha Ω _ hΩc hΩ1 hC₁
  obtain ⟨M₂, hM₂, hsimple⟩ := GlobalTheory.T.reduction_theory_lower_bound F E σ h n J hJ r X Y hW a ha Ω _ hΩc hΩ1 hC₁
  have hact := GlobalTheory.T.rational_unitary_witt_extension F E σ h n J hJ
  refine ⟨_, min c' (min M₁⁻¹ M₂⁻¹), hC₁, lt_min hc' (lt_min (inv_pos.2 hM₁) (inv_pos.2 hM₂)), fun g => ?_⟩
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_near_minimal_vector F E σ h n J hJ r X Y hW g
  obtain ⟨γ₁, hγ₁, hs₁⟩ := GlobalTheory.T.rational_unitary_sends_isotropic F E σ h n J hJ r X Y hW v hv.1 hv.2.1
  obtain ⟨p, hp, k, hk, hg₁⟩ := hIw (γ₁⁻¹ * g)
  obtain ⟨g', q₀, hq₀, s₁, hpe, hconj⟩ := hιdec p hp
  obtain ⟨γ', hγ', q', hq', s', hs', κ', hκ', hg'⟩ := hred' g'
  have hQ : (ι γ')⁻¹ * q₀ * ι γ' * ι q' ∈ minParOne σ J X := mul_mem_one h hJ hW ha (hconj γ') (hι1 q' hq')
  obtain ⟨δ, hδ, hδP, ω, hω, hQe⟩ := hΩ _ hQ
  obtain ⟨e, he, hse⟩ := GlobalTheory.T.minimal_parabolic_scales_isotropic F E σ h n J hJ r X Y hW δ hδ hδP
  set S : Fin (r + 1) → ℝ := Fin.cons s₁ s' with hS
  have hadd : a (Fin.cons s₁ 0) * a (Fin.cons 0 s') = a S := by
    rw [← ha.add]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [hS]
  have hcm : ∀ x, a (Fin.cons s₁ 0) * ι x = ι x * a (Fin.cons s₁ 0) := fun x => hιcomm s₁ x
  have key : δ⁻¹ * ((ι γ')⁻¹ * (γ₁⁻¹ * g)) = ω * a S * (ι κ' * k) := by
    have e1 : γ₁⁻¹ * g = q₀ * ι γ' * ι q' * a S * ι κ' * k := by
      rw [hg₁, hpe, hg', map_mul, map_mul, map_mul, hιt a' ha' s', ← hadd]
      have e2 := hcm γ'
      have e3 := hcm q'
      calc q₀ * a (Fin.cons s₁ 0) * (ι γ' * ι q' * a (Fin.cons 0 s') * ι κ') * k
          = q₀ * (a (Fin.cons s₁ 0) * ι γ') * ι q' * a (Fin.cons 0 s') * ι κ' * k := by group
        _ = q₀ * ι γ' * (a (Fin.cons s₁ 0) * ι q') * a (Fin.cons 0 s') * ι κ' * k := by rw [e2]; group
        _ = _ := by rw [e3]; group
    have e4 : ω = δ⁻¹ * ((ι γ')⁻¹ * q₀ * ι γ' * ι q') := by rw [hQe]; group
    rw [e1, e4]
    group
  have N3 : NearMin σ J (ω * a S * (ι κ' * k)) (e • Xᵀ 0) := by
    rw [← key]
    exact nearMin_rat hact (nearMin_rat hact (nearMin_rat hact hv hγ₁ hs₁) (hιr _ hγ') (hιx _)) hδ hse
  have hκ : ι κ' * k ∈ (ι '' C') * (K : Set (GAd σ J)) := Set.mul_mem_mul ⟨κ', hκ', rfl⟩ hk
  have b1 := hfirst ω hω S _ hκ e he N3
  have b2 := hsimple ω hω S _ hκ e he N3
  have hgeq : g = (γ₁ * ι γ' * δ) * ω * a S * (ι κ' * k) := by
    have : ω * a S * (ι κ' * k) = δ⁻¹ * ((ι γ')⁻¹ * (γ₁⁻¹ * g)) := key.symm
    calc g = (γ₁ * ι γ' * δ) * (δ⁻¹ * ((ι γ')⁻¹ * (γ₁⁻¹ * g))) := by group
      _ = _ := by rw [← this]; group
  refine ⟨γ₁ * ι γ' * δ, mul_mem (mul_mem hγ₁ (hιr _ hγ')) hδ, ω, hΩ1 hω, S, ?_, _, hκ, hgeq⟩
  obtain ⟨-, h2, h3⟩ := hs'
  have hS0 : S 0 = s₁ := rfl
  have hSs : ∀ i : Fin r, S i.succ = s' i := fun i => rfl
  have hc1 : min c' (min M₁⁻¹ M₂⁻¹) ≤ c' := min_le_left _ _
  have hc2 : min c' (min M₁⁻¹ M₂⁻¹) ≤ M₁⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : min c' (min M₁⁻¹ M₂⁻¹) ≤ M₂⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  set c := min c' (min M₁⁻¹ M₂⁻¹) with hcdef
  refine ⟨fun i => Real.exp_pos _, fun i j hij => ?_, fun i hi => ?_⟩
  · refine Fin.cases (motive := fun i => j.val = i.val + 1 → c * Real.exp (S j) ≤ Real.exp (S i)) ?_ (fun i' => ?_) i hij
    · intro hj
      have := b2 j hj
      calc c * Real.exp (S j) ≤ M₂⁻¹ * (M₂ * Real.exp (S 0)) :=
            mul_le_mul hc3 this (Real.exp_pos _).le (inv_pos.2 hM₂).le
        _ = Real.exp (S 0) := by field_simp
    · intro hj
      have hj0 : j ≠ 0 := by
        intro e0
        rw [e0] at hj
        simp at hj
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj0
      have := h2 i' j' (by simpa using hj)
      rw [hSs, hSs]
      exact (mul_le_mul_of_nonneg_right hc1 (Real.exp_pos _).le).trans this
  · refine Fin.cases (motive := fun i => i.val + 1 = r + 1 → c ≤ Real.exp (S i)) ?_ (fun i' => ?_) i hi
    · intro _
      have h4 : Real.exp (-S 0) * Real.exp (S 0) = 1 := by rw [← Real.exp_add]; simp
      have h5 : M₁⁻¹ ≤ Real.exp (S 0) := by
        rw [inv_le_comm₀ hM₁ (Real.exp_pos _)]
        rw [← Real.exp_neg]
        exact b1
      exact hc2.trans h5
    · intro hi'
      rw [hSs]
      exact hc1.trans (h3 i' (by simpa using hi'))

theorem hasRed_zero (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin 0) E} : HasRed σ J X Y := by
  intro a ha
  refine ⟨{1}, 1, isCompact_singleton, one_pos, fun g => ?_⟩
  refine ⟨1, one_mem _, g, ⟨0, fun i => i.elim0, ?_, fun i => i.elim0⟩, 0, ?_, 1, rfl, ?_⟩
  · ext i j
    exact j.elim0
  · exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  · rw [torus_zero ha]
    simp

theorem hasRed_all (h : IsCMExt F E σ) (r : ℕ) : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E),
    IsHermND σ J → IsWittFrame σ J X Y → HasRed σ J X Y := by
  induction r with
  | zero => exact fun n J X Y hJ _ => hasRed_zero h hJ
  | succ r ih => exact fun n J X Y hJ hW => step h hJ hW ih

end GlobalTheory.CompanionTheory.RedCov

namespace GlobalTheory.CompanionTheory.RedCov

theorem torus_neg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
    {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (s : Fin r → ℝ) : a (-s) = (a s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ha.add, neg_add_cancel, torus_zero ha]

theorem conj_mem_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a)
    (s : Fin r → ℝ) {x : GAd σ J} (hx : x ∈ minParOne σ J X) : a s * x * (a s)⁻¹ ∈ minParOne σ J X := by
  obtain ⟨τ, -, h2, h3, h4, h5⟩ := exists_tau h hJ hW ha
  have e : τ (ha.sub h hJ hW s * ⟨x, minParOne_subset hx⟩ * ha.sub h hJ hW (-s)) = 0 := by
    rw [h2, h2, h3, h3, h4 x hx]
    simp
  have := h5 (ha.sub h hJ hW s * ⟨x, minParOne_subset hx⟩ * ha.sub h hJ hW (-s))
  rw [e, torus_zero ha, inv_one, mul_one] at this
  have e2 : ((ha.sub h hJ hW s * ⟨x, minParOne_subset hx⟩ * ha.sub h hJ hW (-s) : minParSub X h hJ hW) : GAd σ J) =
      a s * x * (a s)⁻¹ := by
    rw [← torus_neg ha]
    rfl
  rwa [e2] at this

theorem cov_main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) → (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) → GoodPosition σ J X Y K → ∃ (Ω : Set (GAd σ J)) (c : ℝ), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ 0 < c ∧ ∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ siegelSet σ J X Y Ω c K, g = γ * s := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K hKc hIw _
  obtain ⟨a, ha⟩ := exists_isTorus h hJ hW
  obtain ⟨C, c, hC, hc, hred⟩ := hasRed_all h r n J X Y hJ hW a ha
  obtain ⟨Ω, hΩc, hΩ1, hΩ⟩ := GlobalTheory.T.minimal_parabolic_rational_compact F E σ h n J hJ r X Y hW
  obtain ⟨τ, hτc, hτadd, hτa, hτ1, hτp⟩ := exists_tau h hJ hW ha
  have hD : IsCompact ((C * (K : Set (GAd σ J))) ∩ minPar σ J X) :=
    (hC.mul hKc).inter_right (isClosed_minPar h hJ hW)
  have hT : IsCompact (Subtype.val ⁻¹' ((C * (K : Set (GAd σ J))) ∩ minPar σ J X) : Set (minParSub X h hJ hW)) := by
    have hcl : IsClosed ((minParSub X h hJ hW : Subgroup (GAd σ J)) : Set (GAd σ J)) := isClosed_minPar h hJ hW
    exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  obtain ⟨B, hB⟩ := hT.exists_bound_of_continuousOn hτc.continuousOn
  have hB0 : ∀ p ∈ (Subtype.val ⁻¹' ((C * (K : Set (GAd σ J))) ∩ minPar σ J X) : Set (minParSub X h hJ hW)),
      ∀ i, |τ p i| ≤ max B 0 := fun p hp i =>
    ((norm_le_pi_norm (τ p) i).trans (hB p hp)).trans (le_max_left _ _)
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨Ω, c * Real.exp (-(2 * B')), hΩc, hΩ1, mul_pos hc (Real.exp_pos _), fun g => ?_⟩
  obtain ⟨γ, hγ, q, hq, s, hs, κ, hκ, hg⟩ := hred g
  obtain ⟨p, hp, k, hk, hκe⟩ := hIw κ
  have hpD : p ∈ (C * (K : Set (GAd σ J))) ∩ minPar σ J X := by
    refine ⟨?_, hp⟩
    have : p = κ * k⁻¹ := by rw [hκe]; group
    rw [this]
    exact Set.mul_mem_mul hκ (inv_mem hk)
  set pP : minParSub X h hJ hW := ⟨p, hp⟩ with hpP
  set u := τ pP with hu
  have hub : ∀ i, |u i| ≤ B' := hB0 pP hpD
  have hp1 : p * (a u)⁻¹ ∈ minParOne σ J X := hτp pP
  have hQ := mul_mem_one h hJ hW ha hq (conj_mem_one h hJ hW ha s hp1)
  obtain ⟨δ, hδ, hδP, ω, hω, hQe⟩ := hΩ _ hQ
  have hge : g = (γ * δ) * (ω * a (s + u) * k) := by
    have e1 : γ * δ * (ω * a (s + u) * k) = γ * (δ * ω) * a (s + u) * k := by group
    rw [e1, ← hQe, ha.add, hg, hκe]
    group
  refine ⟨γ * δ, mul_mem hγ hδ, _, ⟨ω, hω, fun i => Real.exp ((s + u) i), ?_, a (s + u), ha.tor _, k, hk, rfl⟩, hge⟩
  obtain ⟨-, h2, h3⟩ := hs
  have hup : ∀ i, Real.exp (u i) ≤ Real.exp B' := fun i => Real.exp_le_exp.2 ((le_abs_self _).trans (hub i))
  have hlo : ∀ i, Real.exp (-B') ≤ Real.exp (u i) := fun i =>
    Real.exp_le_exp.2 (neg_le_of_abs_le (hub i))
  have e2 : Real.exp (-(2 * B')) * Real.exp B' = Real.exp (-B') := by
    rw [← Real.exp_add]; congr 1; ring
  refine ⟨fun i => Real.exp_pos _, fun i j hij => ?_, fun i hi => ?_⟩
  · have a1 := h2 i j hij
    simp only [Pi.add_apply, Real.exp_add]
    calc c * Real.exp (-(2 * B')) * (Real.exp (s j) * Real.exp (u j))
        ≤ c * Real.exp (-(2 * B')) * (Real.exp (s j) * Real.exp B') := by
          gcongr
          exact (le_abs_self _).trans (hub j)
      _ = (c * Real.exp (s j)) * (Real.exp (-(2 * B')) * Real.exp B') := by ring
      _ ≤ Real.exp (s i) * Real.exp (-B') := by
          rw [e2]
          exact mul_le_mul_of_nonneg_right a1 (Real.exp_pos _).le
      _ ≤ Real.exp (s i) * Real.exp (u i) := by
          gcongr
          exact neg_le_of_abs_le (hub i)
  · have a1 := h3 i hi
    simp only [Pi.add_apply, Real.exp_add]
    have e3 : Real.exp (-(2 * B')) ≤ Real.exp (-B') := Real.exp_le_exp.2 (by linarith)
    calc c * Real.exp (-(2 * B')) ≤ c * Real.exp (-B') := by gcongr
      _ ≤ Real.exp (s i) * Real.exp (-B') := mul_le_mul_of_nonneg_right a1 (Real.exp_pos _).le
      _ ≤ Real.exp (s i) * Real.exp (u i) := by
          gcongr
          exact neg_le_of_abs_le (hub i)

end GlobalTheory.CompanionTheory.RedCov

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySiegelDomainExistsStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_siegel_domain_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) → (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) → GoodPosition σ J X Y K → ∃ (Ω : Set (GAd σ J)) (c : ℝ), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ 0 < c ∧ ∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ siegelSet σ J X Y Ω c K, g = γ * s := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.cov_main | exact GlobalTheory.CompanionTheory.RedCov.cov_main | (intros; apply GlobalTheory.CompanionTheory.RedCov.cov_main <;> assumption)
end
