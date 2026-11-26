module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvaluationMap
noncomputable def UpperTheory.Reformulated.B.EvaluationMap.coeffSpan :
    {K W : Type} →
      [inst : Group K] →
        [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module ℂ W] → Representation ℂ K W → Submodule ℂ (K → ℂ) :=
    fun {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W] (ρ : Representation ℂ K W) ↦
      Submodule.span ℂ
        {f : K → ℂ | ∃ (ℓ : Module.Dual ℂ W) (w : W), f = fun (k : K) ↦ (ℓ : W → ℂ) (((ρ : K → W →ₗ[ℂ] W) k : W → W) w)}

namespace UpperTheory.Reformulated.B.EvaluationMap.Helpers

private noncomputable def Φ {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W]
    (ρ : Representation ℂ K W) : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (K → ℂ) where
  toFun φ := fun k => φ (ρ k)
  map_add' φ ψ := by funext k; simp
  map_smul' c φ := by funext k; simp

private noncomputable def evw {W : Type} [AddCommGroup W] [_root_.Module ℂ W]
    (ℓ : Module.Dual ℂ W) (w : W) : Module.Dual ℂ (W →ₗ[ℂ] W) where
  toFun A := ℓ (A w)
  map_add' A B := by simp
  map_smul' c A := by simp

end UpperTheory.Reformulated.B.EvaluationMap.Helpers

open UpperTheory.Reformulated.B.EvaluationMap.Helpers in
theorem UpperTheory.Reformulated.B.EvaluationMap.main :
    ∀ {K W : Type} [inst : Group K] [inst_1 : AddCommGroup W] [inst_2 : _root_.Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ K W), FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ) := by
  intro K W _ _ _ _ ρ
  have hle : UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ ≤ LinearMap.range (Φ ρ) := by
    unfold UpperTheory.Reformulated.B.EvaluationMap.coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨evw ℓ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsKInfEqMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf

open GlobalTheory.Published.AutFin

variable {D : D7}

def kInf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) : GA D V :=
  (Finset.univ.toList.map fun τ => kAt θ V τ (ε τ) (fr τ) (κ τ)).prod

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {ε : D.what₂.Tau → Fin V.rank → Bool}
  {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem kAt_comm (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) (k : Formalism.REAL.KG (ε τ))
    (k' : Formalism.REAL.KG (ε τ')) :
    Commute (kAt θ V τ (ε τ) (fr τ) k) (kAt θ V τ' (ε τ') (fr τ') k') :=
  GlobalTheory.AvgOtherPlace.atTau_comm hθ hne (conj_mem_UH (hfr τ).1 (hfr τ).2 k) (conj_mem_UH (hfr τ').1 (hfr τ').2 k')

theorem exists_kInf_eq_mul (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) (a : D.what₂.Tau) :
    ∃ y : GA D V, ∀ κ' : ∀ τ, Formalism.REAL.KG (ε τ), (∀ τ, τ ≠ a → κ' τ = κ τ) →
      kInf θ V ε fr κ' = y * kAt θ V a (ε a) (fr a) (κ' a) := by
  classical
  let f : (∀ τ, Formalism.REAL.KG (ε τ)) → D.what₂.Tau → GA D V := fun κ τ => kAt θ V τ (ε τ) (fr τ) (κ τ)
  have hperm : (Finset.univ : Finset D.what₂.Tau).toList.Perm (a :: (Finset.univ.erase a).toList) := by
    have := Finset.toList_insert (Finset.notMem_erase a (Finset.univ : Finset D.what₂.Tau))
    rwa [Finset.insert_erase (Finset.mem_univ a)] at this
  refine ⟨((Finset.univ.erase a).toList.map (f κ)).prod, fun κ' hκ' => ?_⟩
  have hpw : ((Finset.univ : Finset D.what₂.Tau).toList.map (f κ')).Pairwise Commute :=
    List.pairwise_map.2 ((Finset.nodup_toList _).imp fun {τ τ'} hne => kAt_comm hθ hfr (Ne.symm hne) _ _)
  have e1 : kInf θ V ε fr κ' = f κ' a * ((Finset.univ.erase a).toList.map (f κ')).prod := by
    rw [kInf, (hperm.map (f κ')).prod_eq' hpw, List.map_cons, List.prod_cons]
  have e2 : (Finset.univ.erase a).toList.map (f κ') = (Finset.univ.erase a).toList.map (f κ) :=
    List.map_congr_left fun τ hτ => by
      simp only [f, hκ' τ (Finset.ne_of_mem_erase (Finset.mem_toList.1 hτ))]
  rw [e1, e2]
  refine (Commute.list_prod_right _ _ fun x hx => ?_).eq
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hx
  exact kAt_comm hθ hfr (Finset.ne_of_mem_erase (Finset.mem_toList.1 hτ)) _ _

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MinimalParabolicUnipotentLeviDecomp
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MinimalParabolicUnipotentLeviDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ComplexOrder

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Published GlobalTheory.Published.AutFin

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa

theorem iwasawa_majorant (n r : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ)
    (hJ : J.IsHermitian) (hJu : IsUnit J.det) (hXX : Xᴴ * J * X = 0) (hXY : Xᴴ * J * Y = 1) (hP : P.PosDef)
    (hPJ : P * J⁻¹ * P = J) (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * J * g = J) :
    ∃ p k : Matrix (Fin n) (Fin n) ℂ, pᴴ * J * p = J ∧ kᴴ * J * k = J ∧ kᴴ * P * k = P ∧
      g = p * k ∧ ∃ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id ∧ p * X = X * B := by
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJi' : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have hJH : (J⁻¹)ᴴ = J⁻¹ := hJ.inv.eq
  have hPH : Pᴴ = P := hP.isHermitian.eq
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg conjTranspose hXY
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hJ.eq, conjTranspose_one, Matrix.mul_assoc] using this
  have hXinj : Function.Injective X.mulVec := fun a b hab => by
    have := congrArg (Matrix.mulVec (Yᴴ * J)) hab
    simpa only [Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec] using this
  have hG : (Xᴴ * P * X).PosDef := hP.conjTranspose_mul_mul_same hXinj
  obtain ⟨R, hRt, hR⟩ := GroundTheory.Automorphic.exists_isUpperTriangular_conjTranspose_mul_self hG
  have hRu : IsUnit R.det := by
    have hd : IsUnit (Rᴴ * R).det := by rw [hR]; exact (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  letI := Matrix.invertibleOfIsUnitDet R hRu
  have hBt : (R⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular hRt
  have hRi : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hRi' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hRiH : (R⁻¹)ᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRi', conjTranspose_one]
  have hX'P : (X * R⁻¹)ᴴ * P * (X * R⁻¹) = 1 := by
    calc (X * R⁻¹)ᴴ * P * (X * R⁻¹) = (R⁻¹)ᴴ * (Xᴴ * P * X) * R⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((R⁻¹)ᴴ * Rᴴ) * (R * R⁻¹) := by rw [← hR]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRiH, hRi', Matrix.one_mul]
  have hX'J : (X * R⁻¹)ᴴ * J * (X * R⁻¹) = 0 := by
    calc (X * R⁻¹)ᴴ * J * (X * R⁻¹) = (R⁻¹)ᴴ * (Xᴴ * J * X) * R⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXX, Matrix.mul_zero, Matrix.zero_mul]
  set X' : Matrix (Fin n) (Fin r) ℂ := X * R⁻¹ with hX'
  have hY'J : (J⁻¹ * (P * X'))ᴴ * J * (J⁻¹ * (P * X')) = 0 := by
    calc (J⁻¹ * (P * X'))ᴴ * J * (J⁻¹ * (P * X')) = X'ᴴ * (P * J⁻¹ * (J * J⁻¹) * P) * X' := by
          simp only [conjTranspose_mul, hJH, hPH, Matrix.mul_assoc]
      _ = 0 := by rw [hJi', Matrix.mul_one, hPJ, hX'J]
  have hXY' : X'ᴴ * J * (J⁻¹ * (P * X')) = 1 := by
    calc X'ᴴ * J * (J⁻¹ * (P * X')) = X'ᴴ * (J * J⁻¹) * P * X' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJi', Matrix.mul_one, hX'P]
  have hPX' : P * X' = J * (J⁻¹ * (P * X')) := by
    rw [← Matrix.mul_assoc J, hJi', Matrix.one_mul]
  obtain ⟨p, k, h1, h2, h3, h4, B, hB, hpB⟩ := GlobalTheory.CompanionTheory.WittIwasawa.iwasawa_witt_flag n r J P X' _ hJ hJu hX'J hY'J hXY' hP hPJ
    hPX' g hg
  refine ⟨p, k, h1, h2, h3, h4, R⁻¹ * B * R, (hBt.mul hB).mul hRt, ?_⟩
  have hXX' : X = X' * R := by rw [hX', Matrix.mul_assoc, hRi, Matrix.mul_one]
  calc p * X = (p * X') * R := by rw [Matrix.mul_assoc, ← hXX']
    _ = X' * (B * R) := by rw [hpB, Matrix.mul_assoc]
    _ = X * (R⁻¹ * B * R) := by simp only [hX', Matrix.mul_assoc]

theorem frame_majorant {n : ℕ} {e : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ} (hf : IsUnit f) :
    (fᴴ * f).PosDef ∧ (fᴴ * f) * (fᴴ * Formalism.REAL.Jm e * f)⁻¹ * (fᴴ * f) = fᴴ * Formalism.REAL.Jm e * f := by
  have hd : IsUnit f.det := (Matrix.isUnit_iff_isUnit_det f).1 hf
  have h1 : f⁻¹ * f = 1 := Matrix.nonsing_inv_mul f hd
  have h2 : f * f⁻¹ = 1 := Matrix.mul_nonsing_inv f hd
  have h3 : fᴴ * (f⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h4 : (f⁻¹)ᴴ * fᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have hJ := Formalism.REAL.Jm_mul_self e
  have hinv : (fᴴ * Formalism.REAL.Jm e * f)⁻¹ = f⁻¹ * Formalism.REAL.Jm e * (f⁻¹)ᴴ := by
    refine Matrix.inv_eq_right_inv ?_
    calc fᴴ * Formalism.REAL.Jm e * f * (f⁻¹ * Formalism.REAL.Jm e * (f⁻¹)ᴴ)
        = fᴴ * Formalism.REAL.Jm e * (f * f⁻¹) * Formalism.REAL.Jm e * (f⁻¹)ᴴ := by simp only [Matrix.mul_assoc]
      _ = fᴴ * (Formalism.REAL.Jm e * Formalism.REAL.Jm e) * (f⁻¹)ᴴ := by
          rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.mul_one, h3]
  refine ⟨?_, ?_⟩
  · have := (Matrix.PosDef.one (n := Fin n) (R := ℂ)).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.2 hf)
    simpa using this
  · rw [hinv]
    calc fᴴ * f * (f⁻¹ * Formalism.REAL.Jm e * (f⁻¹)ᴴ) * (fᴴ * f)
        = fᴴ * (f * f⁻¹) * Formalism.REAL.Jm e * ((f⁻¹)ᴴ * fᴴ) * f := by simp only [Matrix.mul_assoc]
      _ = fᴴ * Formalism.REAL.Jm e * f := by rw [h2, h4, Matrix.mul_one, Matrix.mul_one]

theorem exists_KG_of_stab {n : ℕ} {e : Fin n → Bool} {f k : Matrix (Fin n) (Fin n) ℂ} (hf : IsUnit f)
    (hk1 : kᴴ * (fᴴ * Formalism.REAL.Jm e * f) * k = fᴴ * Formalism.REAL.Jm e * f) (hk2 : kᴴ * (fᴴ * f) * k = fᴴ * f) :
    ∃ κ : Formalism.REAL.KG e, k = f⁻¹ * Formalism.REAL.toMK κ * f := by
  have hd : IsUnit f.det := (Matrix.isUnit_iff_isUnit_det f).1 hf
  have h1 : f⁻¹ * f = 1 := Matrix.nonsing_inv_mul f hd
  have h2 : f * f⁻¹ = 1 := Matrix.mul_nonsing_inv f hd
  have h4 : (f⁻¹)ᴴ * fᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, kᴴ * (fᴴ * M * f) * k = fᴴ * M * f →
      (f * k * f⁻¹)ᴴ * M * (f * k * f⁻¹) = M := fun M hM => by
    calc (f * k * f⁻¹)ᴴ * M * (f * k * f⁻¹) = (f⁻¹)ᴴ * (kᴴ * (fᴴ * M * f) * k) * f⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((f⁻¹)ᴴ * fᴴ) * M * (f * f⁻¹) := by rw [hM]; simp only [Matrix.mul_assoc]
      _ = M := by rw [h4, h2, Matrix.one_mul, Matrix.mul_one]
  have hm1 : (f * k * f⁻¹)ᴴ * (f * k * f⁻¹) = 1 := by
    have := key 1 (by simpa using hk2)
    simpa using this
  have hm2 := key _ hk1
  set m : Matrix (Fin n) (Fin n) ℂ := f * k * f⁻¹ with hm
  have hm3 : m * mᴴ = 1 := mul_eq_one_comm.1 hm1
  have hK : m ∈ Formalism.REAL.Kset e := by
    refine ⟨Matrix.mem_unitaryGroup_iff'.2 hm1, ?_⟩
    calc m * Formalism.REAL.Jm e = m * (mᴴ * Formalism.REAL.Jm e * m) := by rw [hm2]
      _ = (m * mᴴ) * Formalism.REAL.Jm e * m := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm e * m := by rw [hm3, Matrix.one_mul]
  rw [← Formalism.REAL.range_toMK] at hK
  obtain ⟨κ, hκ⟩ := hK
  refine ⟨κ, ?_⟩
  change Formalism.REAL.toMK κ = m at hκ
  rw [hκ, hm]
  calc k = (f⁻¹ * f) * k * (f⁻¹ * f) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = f⁻¹ * (f * k * f⁻¹) * f := by simp only [Matrix.mul_assoc]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}


open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf in
theorem kInf_spec (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) :
    kInf θ V ε fr κ ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (kInf θ V ε fr κ) =
      (fr τ)⁻¹ * Formalism.REAL.toMK (κ τ) * fr τ := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hat := fun τ => isAtTau_kAt θ V hθ τ (hfr τ).1 (hfr τ).2 (κ τ)
  refine ⟨list_prod_mem fun x hx => ?_, fun τ => ?_⟩
  · obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact (hat τ).1
  · have key : ∀ l : List D.what₂.Tau, l.Nodup →
        (τ ∈ l → infMat D.sp.cm.sig V.gram (θ τ) ((l.map fun τ => kAt θ V τ (ε τ) (fr τ) (κ τ)).prod) =
          (fr τ)⁻¹ * Formalism.REAL.toMK (κ τ) * fr τ) ∧
        (τ ∉ l → infMat D.sp.cm.sig V.gram (θ τ) ((l.map fun τ => kAt θ V τ (ε τ) (fr τ) (κ τ)).prod) = 1) := by
      intro l
      induction l with
      | nil =>
        intro _
        exact ⟨fun h => absurd h List.not_mem_nil, fun _ => R.2.2.2.2.1 1 (one_mem _) τ⟩
      | cons a l ih =>
        intro hn
        obtain ⟨ha, hl⟩ := List.nodup_cons.1 hn
        obtain ⟨i1, i2⟩ := ih hl
        rw [List.map_cons, List.prod_cons, R.2.2.2.1]
        by_cases h : a = τ
        · subst h
          exact ⟨fun _ => by rw [(hat a).2.1, i2 ha, Matrix.mul_one], fun hh => absurd List.mem_cons_self hh⟩
        · rw [(hat a).2.2 τ (Ne.symm h), Matrix.one_mul]
          exact ⟨fun hm => i1 (List.mem_of_ne_of_mem (Ne.symm h) hm), fun hm => i2 fun q => hm (List.mem_cons_of_mem _ q)⟩
    exact (key _ (Finset.nodup_toList _)).1 (Finset.mem_toList.2 (Finset.mem_univ τ))

theorem mem_minPar_real (hθ : IsInfFam θ) {r : ℕ} {X : Matrix (Fin V.rank) (Fin r) D.host.E}
    {Q : Matrix (Fin r) (Fin V.rank) D.host.E} (hQ : Q * X = 1) {p : GA D V} (hp : p ∈ GinfC V)
    (h : ∀ ρ, ∃ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id ∧
      infMat D.sp.cm.sig V.gram (θ ρ) p * X.map (tauE D ρ) = X.map (tauE D ρ) * B) :
    p ∈ PositivityTheory.ThKR.minPar D.sp.cm.sig V.gram X := by
  have hs : ∀ w : NumberField.InfinitePlace D.host.F, ∃ (τ : GlobalTheory.AdelicU.EmbOver D.host.E w) (ρ : D.what₂.Tau), τ.1 = tauE D ρ := by
    intro w
    obtain ⟨ρ, rfl⟩ := (GlobalTheory.AdelicU.placeOf_bijective D).2 w
    exact ⟨GlobalTheory.AdelicU.embOverOf D ρ, ρ, rfl⟩
  choose τ ρ hτ using hs
  refine GlobalTheory.CompanionTheory.SiegelArch.mem_minPar_of V.gram (GlobalTheory.AdelicU.isCMExt_host D) τ hp hQ ?_
  intro w
  obtain ⟨B, hB, e⟩ := h (ρ w)
  refine ⟨B, hB, ?_⟩
  rw [hτ w, GlobalTheory.Orb.archMat_eq_archEquiv _ (GlobalTheory.AdelicU.isCMExt_host D), ← GlobalTheory.AdelicU.infMat_infProj,
    ← GlobalTheory.AdelicU.eq_infProj hθ (τ w) (hτ w)]
  exact e

theorem exists_archIwasawa : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ g ∈ GinfC V, ∃ p ∈ PositivityTheory.ThKR.minPar D.sp.cm.sig V.gram X, ∃ κ : (∀ τ, Formalism.REAL.KG (ε τ)), g = p * GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ := by
  intro D θ hθ V ε fr hfr m X Y hW g hg
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hher := fun τ => GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ
  have hmap : ∀ (τ : D.what₂.Tau) {A B : Matrix (Fin V.rank) (Fin m) D.host.E},
      (A.map (tauE D τ))ᴴ * gramAt D V τ * B.map (tauE D τ) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B).map (tauE D τ) := fun τ {A B} => by
    rw [show gramAt D V τ = V.gram.map (tauE D τ) from rfl, Matrix.map_mul, Matrix.map_mul, GlobalTheory.CompanionTheory.SiegelArch.conjT_map hcm]
  have hxx : ∀ τ, (X.map (tauE D τ))ᴴ * gramAt D V τ * X.map (tauE D τ) = 0 := fun τ => by
    rw [hmap, hW.xx]; simp
  have hxy : ∀ τ, (X.map (tauE D τ))ᴴ * gramAt D V τ * Y.map (tauE D τ) = 1 := fun τ => by
    rw [hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyx : ∀ τ, (Y.map (tauE D τ))ᴴ * gramAt D V τ * X.map (tauE D τ) = 1 := fun τ => by
    have h := congrArg conjTranspose (hxy τ)
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hher τ, conjTranspose_one] at h
    rw [Matrix.mul_assoc]
    exact h
  obtain ⟨w₀⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
  obtain ⟨τ₀, -⟩ := (GlobalTheory.AdelicU.placeOf_bijective D).2 w₀
  have hQ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * X = 1 := by
    have h : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * X).map (tauE D τ₀) =
        (1 : Matrix (Fin m) (Fin m) D.host.E).map (tauE D τ₀) := by
      rw [← hmap, hyx, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.map_injective (tauE D τ₀).injective h
  have place : ∀ τ, ∃ (q : Matrix (Fin V.rank) (Fin V.rank) ℂ) (κ : Formalism.REAL.KG (ε τ)),
      infMat D.sp.cm.sig V.gram (θ τ) g = q * ((fr τ)⁻¹ * Formalism.REAL.toMK κ * fr τ) ∧
      ∃ B : Matrix (Fin m) (Fin m) ℂ, B.BlockTriangular id ∧ q * X.map (tauE D τ) = X.map (tauE D τ) * B := by
    intro τ
    have hG : (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ := (hfr τ).2
    obtain ⟨hPd, hPJ⟩ := frame_majorant (e := ε τ) (hfr τ).1
    rw [hG] at hPJ
    obtain ⟨p, k, -, h2, h3, h4, B, hB, hpB⟩ := iwasawa_majorant V.rank m (gramAt D V τ) ((fr τ)ᴴ * fr τ) _ _ (hher τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ) (hxx τ) (hxy τ) hPd hPJ _ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)
    obtain ⟨κ, hκ⟩ := exists_KG_of_stab (e := ε τ) (hfr τ).1 (by rw [hG]; exact h2) h3
    exact ⟨p, κ, hκ ▸ h4, B, hB, hpB⟩
  choose q κ hq2 hq3 using place
  obtain ⟨hk, hkm⟩ := kInf_spec hθ hfr κ
  set k := GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ with hkdef
  refine ⟨g * k⁻¹, ?_, κ, (inv_mul_cancel_right g k).symm⟩
  refine mem_minPar_real hθ hQ (mul_mem hg (inv_mem hk)) fun τ => ?_
  have e : infMat D.sp.cm.sig V.gram (θ τ) (g * k⁻¹) = q τ := by
    have h2 : infMat D.sp.cm.sig V.gram (θ τ) k * infMat D.sp.cm.sig V.gram (θ τ) k⁻¹ = 1 := by
      rw [← R.2.2.2.1, mul_inv_cancel]
      exact R.2.2.2.2.1 1 (one_mem _) τ
    rw [R.2.2.2.1, hq2 τ, ← hkm τ, Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [e]
  exact hq3 τ

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MinimalParabolicUnipotentLeviDecompStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_iwasawa_minimal_parabolic : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ g ∈ GinfC V, ∃ p ∈ PositivityTheory.ThKR.minPar D.sp.cm.sig V.gram X, ∃ κ : (∀ τ, Formalism.REAL.KG (ε τ)), g = p * GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa.exists_archIwasawa | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa.exists_archIwasawa | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa.exists_archIwasawa <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicBlockEmbeddingCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicBlockEmbeddingCompact
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Glob.MinParLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_block_of_triangular {n r s : ℕ} (X : Matrix (Fin n) (Fin r) E) (S : Finset (Fin r)) (hs : s ≤ r)
    {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular id) (e : M * adMat F X = adMat F X * B) :
    ∃ B' : Matrix (Fin s) (Fin s) (AF F ⊗[F] E),
      (B'.BlockTriangular fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) ∧
      M * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B' := by
  refine ⟨B.submatrix (Fin.castLE hs) (Fin.castLE hs), fun i j hij => ?_, Matrix.ext fun x j => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_notMem_of_card_lt_card hij
    have hk1 := Finset.mem_filter.1 hk
    have h2 : k.val < i.val := by simpa [Fin.lt_def] using hk1.2
    have h1 : j.val ≤ k.val := by
      by_contra hc
      exact hk' (Finset.mem_filter.2 ⟨hk1.1, Fin.lt_def.2 (by simpa using not_le.1 hc)⟩)
    exact hB (show Fin.castLE hs j < Fin.castLE hs i from Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega))
  · have e1 := congrFun (congrFun e x) (Fin.castLE hs j)
    have l1 : (M * adMat F (X.submatrix id (Fin.castLE hs))) x j =
        (M * adMat F X) x (Fin.castLE hs j) := rfl
    rw [l1, e1, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) fun i => rfl
    have hi' : s ≤ i.val := by
      by_contra hc
      exact hi ⟨⟨i.val, not_le.1 hc⟩, rfl⟩
    have hz : B i (Fin.castLE hs j) = 0 :=
      hB (show Fin.castLE hs j < i by rw [Fin.lt_def]; simp only [Fin.val_castLE]; omega)
    rw [hz, mul_zero]

theorem minPar_eq_unip_mul_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)), ∀ p ∈ PositivityTheory.ThKR.minPar σ J X, ∃ u ∈ GlobalTheory.StdPar.unip σ J X S, ∃ l ∈ GlobalTheory.StdPar.levi σ J X Y S, p = u * l := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S p hp
  obtain ⟨s, hs, hS⟩ : ∃ s, ∃ hs : s ≤ r, ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k := by
    refine ⟨S.sup fun k => k.val + 1, Finset.sup_le fun k _ => k.2, fun i => ?_⟩
    rw [Finset.lt_sup_iff]
    exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS
    (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) fun _ => rfl
  have hp' : p ∈ parFlag σ J (X.submatrix id (Fin.castLE hs))
      (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) := by
    obtain ⟨B, hB, e⟩ := hp
    obtain ⟨B', hB', e'⟩ := PositivityTheory.ThKR.inv_mem_minPar h hJ hW (show p ∈ PositivityTheory.ThKR.minPar σ J X from ⟨B, hB, e⟩)
    exact ⟨exists_block_of_triangular X S hs hB e, exists_block_of_triangular X S hs hB' e'⟩
  obtain ⟨u, hu', m, hm, e, -⟩ := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs))
    (Y.submatrix id (Fin.castLE hs)) (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).1 p hp'
  exact ⟨u, hu ▸ hu', m, hl ▸ hm, e⟩

end GlobalTheory.CompanionTheory.Glob.MinParLevi
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicBlockEmbeddingCompactStatement
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_unipotent_levi_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)), ∀ p ∈ PositivityTheory.ThKR.minPar σ J X, ∃ u ∈ GlobalTheory.StdPar.unip σ J X S, ∃ l ∈ GlobalTheory.StdPar.levi σ J X Y S, p = u * l := by
  first | exact @GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi | exact GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi | (intros; apply GlobalTheory.CompanionTheory.Glob.MinParLevi.minPar_eq_unip_mul_levi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviPartsCommute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped Pointwise

theorem exists_finset_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Set G}
    (hK : IsCompact K) {U : Subgroup G} (hU : IsOpen (U : Set G)) :
    ∃ C : Finset G, (C : Set G) ⊆ K ∧ ∀ k ∈ K, ∃ c ∈ C, ∃ u ∈ U, k = c * u := by
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : K => (k : G) • (U : Set G)) (fun k => hU.smul _)
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, U.one_mem, mul_one x⟩⟩
  refine ⟨t.image Subtype.val, by simp, fun k hk => ?_⟩
  obtain ⟨c, hc, hkc⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨u, hu, e⟩ := Set.mem_smul_set.1 hkc
  exact ⟨c, Finset.mem_image_of_mem _ hc, u, hu, e.symm⟩

theorem kInf_mem_GinfC {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {V : HSp D}
    {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsFrameFam V ε fr)
    (κ : ∀ τ, Formalism.REAL.KG (ε τ)) : kInf θ V ε fr κ ∈ GinfC V := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact (isAtTau_kAt θ V hθ τ (hfr τ).1 (hfr τ).2 (κ τ)).1

theorem mul_mem_minPar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {X : Matrix (Fin n) (Fin r) E} {p q : GlobalTheory.AdelicU.GAd σ J}
    (hp : p ∈ PositivityTheory.ThKR.minPar σ J X) (hq : q ∈ PositivityTheory.ThKR.minPar σ J X) : p * q ∈ PositivityTheory.ThKR.minPar σ J X := by
  obtain ⟨B, hB, eB⟩ := hp
  obtain ⟨B', hB', eB'⟩ := hq
  refine ⟨B * B', hB.mul hB', ?_⟩
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, eB', ← Matrix.mul_assoc, eB, Matrix.mul_assoc]

theorem exists_iwasawa : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∃ K : Subgroup (GA D V), IsCompact (K : Set (GA D V)) ∧ K ≤ GfC V ∧ ∀ g : GA D V, ∃ p ∈ PositivityTheory.ThKR.minPar D.sp.cm.sig V.gram X, ∃ κ : (∀ τ, Formalism.REAL.KG (ε τ)), ∃ k ∈ K, g = p * GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ * k := by
  intro D θ hθ V ε fr hfr m X Y hW
  have hh := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨K, hKf, hK, hiw, -⟩ := GlobalTheory.T.unitary_adelic_iwasawa_compact D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW
  refine ⟨K, hK, hKf, fun g => ?_⟩
  obtain ⟨p, hp, κ, e1⟩ := GlobalTheory.T.archimedean_iwasawa_minimal_parabolic D θ hθ V ε fr hfr m X Y hW _ (GlobalTheory.AutMult.toInf V g).2
  obtain ⟨q, hq, hqf, k, hk, e2⟩ := hiw _ (GlobalTheory.AutMult.toFin V g).2
  refine ⟨p * q, mul_mem_minPar hp hq, κ, k, hk, ?_⟩
  have hcomm := GlobalTheory.AutMult.commute_inf_fin (⟨_, kInf_mem_GinfC hθ hfr κ⟩ : GinfC V) ⟨q, hqf⟩
  rw [← GlobalTheory.AutMult.toInf_mul_toFin g, e1, e2, mul_assoc p, ← mul_assoc _ q k, hcomm.eq]
  simp only [mul_assoc]

theorem exists_decomp : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ C : Finset (GA D V), ∀ g : GA D V, ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ l ∈ levi D.sp.cm.sig V.gram X Y T, ∃ c ∈ C, ∃ κ : (∀ τ, Formalism.REAL.KG (ε τ)), ∃ u ∈ U, u ∈ GfC V ∧ g = n * l * c * GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ * u := by
  intro D θ hθ V U hU ε fr hfr m X Y hW T
  classical
  have hh := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨K, hK, hKf, hiw⟩ := exists_iwasawa D θ hθ V ε fr hfr m X Y hW
  obtain ⟨C, hCK, hC⟩ := exists_finset_cosets hK hU
  refine ⟨C, fun g => ?_⟩
  obtain ⟨p, hp, κ, k, hk, rfl⟩ := hiw g
  obtain ⟨c, hc, u, hu, rfl⟩ := hC k hk
  obtain ⟨n, hn, l, hl, rfl⟩ := GlobalTheory.T.minimal_parabolic_unipotent_levi_decomp D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW T p hp
  have hcf : c ∈ GfC V := hKf (hCK hc)
  have huf : u ∈ GfC V := by
    have := mul_mem (inv_mem hcf) (hKf hk)
    rwa [inv_mul_cancel_left] at this
  refine ⟨n, hn, l, hl, c, hc, κ, u, hu, huf, ?_⟩
  have hcomm := GlobalTheory.AutMult.commute_inf_fin (⟨_, kInf_mem_GinfC hθ hfr κ⟩ : GinfC V) ⟨c, hcf⟩
  simp only [mul_assoc]
  rw [← mul_assoc (kInf θ V ε fr κ) c u, hcomm.eq, mul_assoc]

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) :=
  _root_.UpperTheory.Reformulated.B.EvaluationMap.main ρ

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}


open Classical in
theorem eq_zero_of_kInf {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)} (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) {φ : GA D V → ℂ}
    (htype : ∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) (S : ∀ τ, Finset (Formalism.REAL.KG (ε τ)))
    (hS : ∀ τ, ∀ f ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ τ), (∀ x ∈ S τ, f x = 0) → f = 0) (x : GA D V)
    (h : ∀ s ∈ Fintype.piFinset S, φ (x * kInf θ V ε fr s) = 0) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) :
    φ (x * kInf θ V ε fr κ) = 0 := by
  classical
  suffices key : ∀ I : Finset D.what₂.Tau, ∀ κ : ∀ τ, Formalism.REAL.KG (ε τ), (∀ τ, τ ∉ I → κ τ ∈ S τ) →
      φ (x * kInf θ V ε fr κ) = 0 from key Finset.univ κ (by simp)
  intro I
  induction I using Finset.induction_on with
  | empty => exact fun κ hκ => h κ (Fintype.mem_piFinset.2 fun τ => hκ τ (by simp))
  | insert a I _ ih =>
    intro κ hκ
    obtain ⟨y, hy⟩ := exists_kInf_eq_mul hθ hfr κ a
    have h0 := hS a _ (htype a (x * y)) fun t ht => by
      have e := hy (Function.update κ a t) fun τ hτ => Function.update_of_ne hτ _ _
      rw [Function.update_self] at e
      show φ (x * y * kAt θ V a (ε a) (fr a) t) = 0
      rw [mul_assoc, ← e]
      refine ih _ fun τ hτ => ?_
      by_cases e' : τ = a
      · subst e'; simpa using ht
      · rw [Function.update_of_ne e']; exact hκ τ (by simp [e', hτ])
    rw [hy κ fun _ _ => rfl, ← mul_assoc]
    exact congrFun h0 (κ a)

theorem exists_finset_sep_levi : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∃ B : Finset (GA D V), ∀ φ ∈ formsOn θ V X Y T U ε fr ρ c, (∀ b ∈ B, ∀ g ∈ levi D.sp.cm.sig V.gram X Y T, φ (g * b) = 0) → φ = 0 := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hW T hT
  classical
  obtain ⟨C, hC⟩ := exists_decomp D θ hθ V U hU ε fr hfr m X Y hW T
  haveI := fun τ => finiteDimensional_coeffSpan (ρ τ)
  choose S hS using fun τ => exists_finset_sep (GlobalTheory.Published.AutFin.coeffSpan (ρ τ))
  refine ⟨(C ×ˢ Fintype.piFinset S).image fun p => p.1 * kInf θ V ε fr p.2, fun φ hφ h0 => ?_⟩
  funext g
  obtain ⟨n, hn, l, hl, c', hc, κ, u, hu, hu', rfl⟩ := hC g
  rw [hφ.2.1 u hu hu', mul_assoc (n * l), mul_assoc n, hφ.1.left n (Subgroup.mem_sup_left hn), ← mul_assoc]
  refine eq_zero_of_kInf hθ hfr hφ.2.2.1 S hS (l * c') (fun s hs => ?_) κ
  rw [mul_assoc]
  exact h0 _ (Finset.mem_image.2 ⟨(c', s), Finset.mem_product.2 ⟨hc, hs⟩, rfl⟩) l hl

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviPartsCommuteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_frame_K_type_decomposition : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∃ B : Finset (GA D V), ∀ φ ∈ formsOn θ V X Y T U ε fr ρ c, (∀ b ∈ B, ∀ g ∈ levi D.sp.cm.sig V.gram X Y T, φ (g * b) = 0) → φ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep.exists_finset_sep_levi | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep.exists_finset_sep_levi | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep.exists_finset_sep_levi <;> assumption)
end
