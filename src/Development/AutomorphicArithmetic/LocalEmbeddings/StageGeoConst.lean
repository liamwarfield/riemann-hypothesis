module

public import Development.AutomorphicArithmetic.DivisorFrames.ExistsThOEqOfIsLatVacThetaFun
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelFiniteExponent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsSeesawIntertwinersOfTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsSBHalfThetaOfSelfDualLattices

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.TripleDualCoordSplitPlacesOfIsPairIsLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem piW_cA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : AE D) :
    piW t (cA D w) = piW (t.comp D.sp.cm.sig) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem piW_incA' {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (e : D.host.E) : piW t (incA D e) = t e := by
  change GlobalTheory.AdelicU.evFin D.host.F v 1 * t e = t e
  simp

private theorem coord_eq {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)} (t : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (A' WW : HSp D) {d : ℕ} (e : Fin d ≃ Fin WW.rank)
    (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (y : WO A' WW) :
    (βA'⁻¹).1.map (evW t) * (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) *
        ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ * (βW.1.map (evW t)).submatrix e e =
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (evW t)).submatrix id e := by
  have hG : (A'.gram⁻¹)ᴴ = A'.gram⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    congr 1
    refine Matrix.ext fun i j => ?_
    exact GlobalTheory.DualPairCheck.gram_star A' j i
  have h0 : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (A'.gram⁻¹))ᵀ).map (piW (t.comp D.sp.cm.sig)) = (A'.gram⁻¹).map t := by
    refine Matrix.ext fun i j => ?_
    have h := congrFun (congrFun hG i) j
    change piW (t.comp D.sp.cm.sig) (incA D (A'.gram⁻¹ j i)) = t (A'.gram⁻¹ i j)
    rw [piW_incA', ← h]
    rfl
  have h2 : (ptO A'.gram e y).map (piW (t.comp D.sp.cm.sig)) =
      ((A'.gram⁻¹).map t * ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig))).submatrix id e := by
    rw [← h0, ← Matrix.map_mul, ← Matrix.transpose_mul]
    rfl
  have h3 : ((D.host.xi0 • (WW.gramᵀ).submatrix e e).map t)ᵀ = t D.host.xi0 • (WW.gram.map t).submatrix e e := by
    refine Matrix.ext fun i j => ?_
    simp
  have hinc : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) D.host.E),
      ((M.map (incA D)).map (toEAf D)).map (evW t) = M.map t := by
    intro p q M
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, GlobalTheory.BotMatch.evW_toEAf, piW_incA']
  have hy : ((((y : Matrix _ _ (AE D)).map (cA D))ᵀ).map (toEAf D)).map (evW t) =
      ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.transpose_apply, GlobalTheory.BotMatch.evW_toEAf, piW_cA']
  have hxi : evW t (eToEAf D D.host.xi0) = t D.host.xi0 := by
    rw [← piW_incA' t, ← GlobalTheory.BotMatch.evW_toEAf]
    rfl
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (evW t) =
      t D.host.xi0 • ((βA'⁻¹).1.map (evW t) * ((A'.gram⁻¹).map t *
        ((y : Matrix _ _ (AE D))ᵀ).map (piW (t.comp D.sp.cm.sig)) * WW.gram.map t) * βW.1.map (evW t)) := by
    rw [← hxi, ← hinc, ← hinc, ← hy, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul]
    refine Matrix.ext fun i j => ?_
    exact map_mul (evW t) _ _
  rw [h1, h2, h3, Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul]
  simp only [Pi.smul_apply]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_assoc]
  rfl

theorem UpperTheory.triple_dualCoord_split_places_of_isPair_isLat :
    ∀ (D : D7) (T : Type) (A A' WW : HSp D) (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
        (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))),
        X.Is ψ θ α β νH S → ∀ (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E)
        (Vs : Spc D.host.F D.host.E A'.rank) (Ws : Spc D.host.F D.host.E (A.rank + A'.rank)) (M : Model D.sp.cm.sig Vs Ws),
        IsPair ψ false A' WW (finCongr hr) Bs Vs Ws M → IsLat (finCongr hr) Vs Ws X.rA'.Λ X.rW.Λ →
        ∀ (t : T) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (τ : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ w, w ∈ S t ↔ ∃ v : P, splitPrime (τ v) = w) →
        ∀ (b : ∀ v : P, GL (Fin A'.rank) (Fv D.host.F v)) (c : ∀ v : P, GL (Fin (A.rank + A'.rank)) (Fv D.host.F v))
          (ι : ∀ v : P, ((Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ) →ₗ[ℂ]
            (Matrix (Fin A'.rank) (Fin (A.rank + A'.rank)) (Fv D.host.F v) → ℂ)),
        (∀ v, ((b v)⁻¹).1 = (A'.gram.map (τ v) * X.rA'.β.1.map (evW (τ v)))ᵀ) →
        (∀ v, (c v).1 = (X.rW.β.1.map (evW (τ v))).submatrix (finCongr hr) (finCongr hr)) →
        (∀ v, M.IsLinBar ψ (τ v) (b v) (c v) (ι v)) → (∀ v : P, ι v (M.vac v) 0 = 1) →
        ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, v ∉ P → φ v = M.vac v) →
        (∀ v : P, ι v (φ v) = GlobalTheory.StdPairCone.stdB (chrW (α t / β t) (τ v)) (unifAt v.1) (X.c t (splitPrime (τ v))) A.rank A'.rank) →
        ∀ g : SInf D.host.F (Fin A'.rank × Fin (A.rank + A'.rank)),
        X.vac' = thO M ψ (sgn false A').gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) →
        X.f' t = thO M ψ (sgn false A').gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) := by
  intro D T A A' WW X ψ θ α β νH S hX hr Bs Vs Ws M hp hl t P τ hS b c ι hb hc hι h1 φ hφ hφP hstd g hvac
  have hP : ∀ v, v ∈ P ↔ ∃ w ∈ S t, w.under (𝓞 D.host.F) = v := fun v =>
    ⟨fun hv => ⟨_, (hS _).2 ⟨⟨v, hv⟩, rfl⟩, GlobalTheory.AdelicU.splitPrime_under _⟩, by
      rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := (hS w).1 hw
      rw [GlobalTheory.AdelicU.splitPrime_under]
      exact u.2⟩
  have hinj : Function.Injective (fun v : P => splitPrime (τ v)) := fun u v h =>
    Subtype.ext ((GlobalTheory.AdelicU.splitPrime_under (τ u)).symm.trans
      ((congrArg (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.under (𝓞 D.host.F)) h).trans (GlobalTheory.AdelicU.splitPrime_under (τ v))))
  obtain ⟨hh1, hh0⟩ := UpperTheory.idempotentSum_fixes_iff_halfEl D (X.e t) (S t) (hX.idem t) P τ hP fun v => (hS _).2 ⟨v, rfl⟩
  have hdet : ∀ v : P, ((Ws.J.map (τ v))ᵀ).det ≠ 0 := fun v => by
    have h0 : Ws.J.det ≠ 0 := by
      rw [hp.JW, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero) (GlobalTheory.LatVac.gram_det_isUnit WW).ne_zero
    rw [Matrix.det_transpose]
    have h2 := (τ v).toRingHom.map_det Ws.J
    exact fun h => h0 ((τ v).toRingHom.injective ((h2.trans h).trans (map_zero _).symm))
  have hbb : ∀ v : P, -((b v).1ᵀ * Vs.J.map (τ v)) = (X.rA'.β⁻¹).1.map (evW (τ v)) := fun v => by
    have e1 : Vs.J.map (τ v) = -(A'.gram.map (τ v)) := by
      rw [hp.JV]
      refine Matrix.ext fun i j => ?_
      simp
    have e2 : (b v).1ᵀ * (A'.gram.map (τ v) * X.rA'.β.1.map (evW (τ v))) = 1 := by
      rw [← Matrix.transpose_transpose (A'.gram.map (τ v) * _), ← hb v, ← Matrix.transpose_mul, Units.inv_mul,
        Matrix.transpose_one]
    have e3 : X.rA'.β.1.map (evW (τ v)) * (X.rA'.β⁻¹).1.map (evW (τ v)) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e1, Matrix.mul_neg, neg_neg, ← Matrix.mul_one (_ * A'.gram.map (τ v)), ← e3, ← Matrix.mul_assoc,
      Matrix.mul_assoc (b v).1ᵀ, e2, Matrix.one_mul]
  refine UpperTheory.exists_isSBHalf_theta_of_selfDual_lattices D ψ false A' WW _ (finCongr hr) Bs Vs Ws M hp X.rA'.Λ X.rW.Λ hl hX.rigA'.1 hX.rigW.1 P
    (fun v => (τ v).comp D.sp.cm.sig) τ (fun v x => congrArg (τ v) (star_star x).symm) (cA D (X.e t)) hh0
    (fun z => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hh1 z)
    (fun v => Matrix.GeneralLinearGroup.map (evW (τ v)) X.rA'.β⁻¹)
    (fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet v) * c v) ι (fun v => ?_) h1 φ hφ hφP g
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (X.e t) (X.ideal S t) A.rank A' WW X.rA'.β X.rW.β) (X.f' t) (fun x => ?_) ?_
  · have h := hι v
    unfold Model.IsLinBar at h
    convert h using 1
    funext u
    change (X.rA'.β⁻¹).1.map (evW (τ v)) * _ * ((Ws.J.map (τ v))ᵀ * (c v).1) = _
    rw [← hbb v]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
  · by_cases hx : IsHalf (cA D (X.e t)) x
    · rw [if_pos hx]
      refine (UpperTheory.stdSectionSecond_eq_prod_local D (X.e t) (S t) (hX.idem t) P (fun v => v.1) τ hS hinj (X.c t) (α t / β t) A.rank A' WW
        X.rA'.β X.rW.β hr x hx).trans (Finset.prod_congr rfl fun v _ => ?_)
      rw [hstd v, ← coord_eq, ← hc v, ← hp.JW, Matrix.mul_assoc]
      rfl
    · rw [if_neg hx]
      exact if_neg fun h => hx h.1
  · rw [← hvac]
    exact hX.snd t
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ThetaLiftTripleLocalSplitPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fmFst_mat {k : Type} [Field k] {a n d : ℕ} (e : Fin n ≃ Fin d) (B G Gi : Matrix (Fin a) (Fin a) k) (hG : Gi * G = 1)
    (W Wi : Matrix (Fin d) (Fin d) k) (hW : Wi * W = 1) (m : GL (Fin n) k) (hm : m.1 = W.submatrix e e)
    (X : Matrix (Fin d) (Fin a) k) :
    (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e * (GlobalTheory.SplitFlip.invT m).1 = ((Wi * X * B)ᵀ).submatrix id e := by
  have h1 : (m⁻¹).1 = Wi.submatrix e e := by
    have : Wi.submatrix e e * m.1 = 1 := by
      rw [hm, Matrix.submatrix_mul_equiv, hW]; exact Matrix.submatrix_one_equiv e
    calc (m⁻¹).1 = (Wi.submatrix e e * m.1) * (m⁻¹).1 := by rw [this, Matrix.one_mul]
      _ = Wi.submatrix e e := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h2 : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((X * B)ᵀ).submatrix id e := by
    have : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((G * B)ᵀ * (X * Gi)ᵀ).submatrix id e := rfl
    rw [this, ← Matrix.transpose_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Gi, hG, Matrix.one_mul]
  rw [h2, GlobalTheory.SplitFlip.invT_val, h1, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul,
    Matrix.mul_assoc]

private theorem selfDual_neg {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSelfDualC V Λ) : IsSelfDualC (sgn true V) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
  have e : ∑ i, ∑ j, star (x i) * (sgn true V).gram i j * y j = -∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show star (x i) * (-V.gram i j) * y j = _
    ring
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩, fun ⟨b, hb⟩ => ⟨-b, by simp [hb]⟩⟩

theorem UpperTheory.thetaLift_triple_local_split_places :
    ∀ (D : D7) (T : Type) (A A' WW : HSp D) (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
        (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))),
        X.Is ψ θ α β νH S → ∀ (hr : A.rank + A'.rank = WW.rank) (Bs : Base D.host.F D.host.E)
        (Vs : Spc D.host.F D.host.E A.rank) (Ws : Spc D.host.F D.host.E (A.rank + A'.rank)) (M : Model D.sp.cm.sig Vs Ws),
        IsPair ψ true A WW (finCongr hr) Bs Vs Ws M → IsLat (finCongr hr) Vs Ws X.rA.Λ X.rW.Λ →
        ∀ (t : T) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (τ : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ w, w ∈ S t ↔ ∃ v : P, splitPrime (τ v) = w) →
        ∀ (b : ∀ v : P, GL (Fin A.rank) (Fv D.host.F v)) (c : ∀ v : P, GL (Fin (A.rank + A'.rank)) (Fv D.host.F v))
          (ι : ∀ v : P, ((Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ) →ₗ[ℂ]
            (Matrix (Fin A.rank) (Fin (A.rank + A'.rank)) (Fv D.host.F v) → ℂ)),
        (∀ v, ((b v)⁻¹).1 = -(A.gram.map (τ v) * X.rA.β.1.map (evW (τ v)))ᵀ) →
        (∀ v, (c v).1 = (X.rW.β.1.map (evW (τ v))).submatrix (finCongr hr) (finCongr hr)) →
        (∀ v, M.IsLinW ψ (τ v) (b v) (c v) (ι v)) → (∀ v : P, ι v (M.vac v) 0 = 1) →
        ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, v ∉ P → φ v = M.vac v) →
        (∀ v : P, ι v (φ v) = GlobalTheory.StdPairCone.stdA (chrW (α t / β t) (τ v)) (unifAt v.1) (X.c t (splitPrime (τ v))) A.rank A'.rank) →
        ∀ g : SInf D.host.F (Fin A.rank × Fin (A.rank + A'.rank)),
        X.vac = thO M ψ (sgn true A).gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) →
        X.f t = thO M ψ (sgn true A).gram (finCongr hr) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) := by
  intro D T A A' WW X ψ θ α β νH S hX hr Bs Vs Ws M hP hL t P τ hS b c ι hb hc hι hι0 φ hφ hφ' hφA g hvac
  have hPS : ∀ v, v ∈ P ↔ ∃ w ∈ S t, w.under (𝓞 D.host.F) = v := fun v => by
    constructor
    · intro hv
      exact ⟨splitPrime (τ ⟨v, hv⟩), (hS _).2 ⟨_, rfl⟩, GlobalTheory.AdelicU.splitPrime_under (τ ⟨v, hv⟩)⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := (hS w).1 hw
      rw [GlobalTheory.AdelicU.splitPrime_under (τ u)]
      exact u.2
  have hτS : ∀ v : P, splitPrime (τ v) ∈ S t := fun v => (hS _).2 ⟨v, rfl⟩
  have hinj : Function.Injective fun v : P => splitPrime (τ v) := fun u v h => by
    have h1 := GlobalTheory.AdelicU.splitPrime_under (τ u)
    have h2 := GlobalTheory.AdelicU.splitPrime_under (τ v)
    have h' : splitPrime (τ u) = splitPrime (τ v) := h
    exact Subtype.ext (h1.symm.trans (h' ▸ h2))
  obtain ⟨hh0, hh1⟩ := UpperTheory.idempotentSum_fixes_iff_halfEl D (X.e t) (S t) (hX.idem t) P τ hPS hτS
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin A.rank) (Fin A.rank) D.host.E, G = (sgn true A).gram := ⟨_, rfl⟩
  have hdet : IsUnit G.det := by rw [hG]; exact (Formalism.L2.Theta.gram_det_ne (sgn true A)).isUnit
  have hGi : ∀ v : P, (G⁻¹.map (incA D)).map (piW (τ v)) * (G.map (incA D)).map (piW (τ v)) = 1 := fun v => by
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hbG : ∀ v : P, ((b v)⁻¹).1 = ((G.map (incA D)).map (piW (τ v)) * X.rA.β.1.map (evW (τ v)))ᵀ := fun v => by
    have e0 : (G.map (incA D)).map (piW (τ v)) = -A.gram.map (τ v) := by
      refine Matrix.ext fun i j => ?_
      have e1 : G i j = -A.gram i j := by rw [hG]; rfl
      have e2 : ∀ y, piW (τ v) (incA D y) = τ v y := fun y => one_mul (τ v y)
      show piW (τ v) (incA D (G i j)) = -(τ v (A.gram i j))
      rw [e2, e1, map_neg]
    rw [hb, e0, Matrix.neg_mul, Matrix.transpose_neg]
  have key : ∀ (x : WO A WW) (v : P),
      ((b v)⁻¹).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (τ v)) * (GlobalTheory.SplitFlip.invT (c v)).1 =
      (((frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)))ᵀ).submatrix id (finCongr hr) := fun x v => by
    have e1 : (ptO G (finCongr hr) x).map (piW (τ v)) =
        ((Matrix.map x (piW (τ v)) * (G⁻¹.map (incA D)).map (piW (τ v)))ᵀ).submatrix id (finCongr hr) := by
      rw [← Matrix.map_mul]; rfl
    have e2 : (frMapO A WW X.rA.β X.rW.β x).map (evW (τ v)) =
        (X.rW.β⁻¹).1.map (evW (τ v)) * Matrix.map x (piW (τ v)) * X.rA.β.1.map (evW (τ v)) := by
      unfold frMapO
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 2
      refine Matrix.ext fun i j => ?_
      exact GlobalTheory.BotMatch.evW_toEAf (τ v) (x i j)
    rw [← hG, hbG, e1, e2]
    refine fmFst_mat (finCongr hr) _ _ _ (hGi v) (X.rW.β.1.map (evW (τ v))) _ ?_ (c v) (hc v) _
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hth := hX.fst t
  rw [hvac] at hth
  refine UpperTheory.exists_isSBHalf_theta_of_selfDual_lattices D ψ true A WW _ (finCongr hr) Bs Vs Ws M hP X.rA.Λ X.rW.Λ hL (selfDual_neg hX.rigA.1) hX.rigW.1
    P τ (fun v => (τ v).comp D.sp.cm.sig) (fun _ _ => rfl) (X.e t) hh0 hh1 (fun v => (b v)⁻¹)
    (fun v => GlobalTheory.SplitFlip.invT (c v)) ι (fun v => hι v) hι0 φ hφ hφ' g
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (X.e t) (X.ideal S t) A WW X.rA.β X.rW.β) (X.f t) (fun x => ?_) hth
  by_cases hx : IsHalf (X.e t) x
  · rw [if_pos hx]
    refine (UpperTheory.stdSectionFirst_eq_prod_local D (X.e t) (S t) (hX.idem t) P (fun v => v.1) τ hS hinj (X.c t) (α t / β t) A WW X.rA.β X.rW.β
      A'.rank hr x hx).trans (Finset.prod_congr rfl fun v _ => ?_)
    rw [hφA v]
    exact congrArg _ (key x v).symm
  · rw [if_neg hx]
    exact if_neg fun h => hx h.1
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ThetaLiftPureTensorOfIsFinF
section SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At evI realAd SInf ActsD piInf Spc Model)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealDict GlobalTheory.RealDict.FockMap

private theorem finPart_ne {F : Type} [Field F] [NumberField F] {n d : ℕ}
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y, GlobalTheory.BigNZ.finPartFn φ y ≠ 0 := by
  classical
  choose ξ hξ using fun v => Function.ne_iff.1 (h0 v)
  have hS := Filter.eventually_cofinite.1 hs
  let y : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)
  refine ⟨y, ?_⟩
  refine finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
  by_cases hv : v ∈ hS.toFinset
  · have : (fun k => evalV F v (y k)) = ξ v := funext fun k => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]
    rw [this]
    exact hξ v
  · have : (fun k => evalV F v (y k)) = 0 := funext fun k => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _
    rw [this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]
    exact one_ne_zero


set_option maxHeartbeats 1000000 in
private theorem fock_of {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {M X : HSp D} {Xs : Spc D.host.F D.host.E M.rank}
    {Ws : Spc D.host.F D.host.E X.rank} (Mo : Model D.sp.cm.sig Xs Ws)
    (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr M) (B : Fr X)
    {τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w} (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig)
    (hStd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hX : Xs.J = sgE (D := D) ε • M.gram)
    (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (hM : Mo.IsGood ψ) (h2X : ∀ w, Xs.θ w * Xs.θ w = 1) (h2W : ∀ w, Ws.θ w * Ws.θ w = 1)
    (hc : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
      Ws.θ w = (B.cart t).map conj)
    (g₀ : SInf D.host.F (Fin M.rank × Fin X.rank)) (g0 : g₀ ≠ 0)
    {g : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ} (hg : g ∈ SB _) (hy : ∃ y, g y ≠ 0)
    (hv : IsVacF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g))) :
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank),
      LinearMap.range Φ = Mo.Pol ψ τ ∧
      ∀ g' : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ, g' ∈ SB _ →
        ∀ P, th ψ ε Mo (pureA D.host.F (Φ P) g') = ptF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g')) P := by
  obtain ⟨-, -, tinj, tth, -⟩ := th_laws Mo hψ hθ hX hW hM
  obtain ⟨Dr, hD1, hD2, hD3⟩ := exists_der Mo hStd
  obtain ⟨y, hy⟩ := hy
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = thL Mo hψ hθ hX hW hM hg := ⟨_, rfl⟩
  have hΘ' : ∀ f : SInf D.host.F (Fin M.rank × Fin X.rank), th ψ ε Mo (pureA D.host.F f g) = Θ f := fun f => by rw [hΘ]; rfl
  rw [hΘ'] at hv
  have hd : ∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f) :=
    hΘ ▸ dRho_thL Mo hψ hθ hX hW hM hD1 hg
  have hi : Function.Injective Θ := fun f f' h => by
    have e := tinj _ (pureA_mem f hg) _ (pureA_mem f' hg) (by rw [hΘ] at h; exact h)
    refine DFunLike.ext _ _ fun a => ?_
    have e2 := congrFun e (GlobalTheory.RealLift.ptAt a y)
    rw [GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt] at e2
    exact mul_right_cancel₀ hy e2
  have hg₀ : ∀ t z, Dr (dir ε M X θ t z) g₀ +
      Complex.I • Dr (dir ε M X θ t (cplxO ((frSgn ε A).cart t) (B.cart t) z)) g₀ = 0 := fun t z => hi (by
    have h : annih (heisO ψ (sgn ε M) X) θ t (cplxO ((frSgn ε A).cart t) (B.cart t)) z (Θ g₀) = 0 := hv.2 t z
    rw [annih, hd, hd, ← map_smul, ← map_add (f := _)] at h
    rw [h, map_zero])
  let um : FVar D X.rank M.rank → Matrix (Fin X.rank) (Fin M.rank) ℂ := fun k =>
    Formalism.IndefR.Datum.unitMap ((frSgn ε A).onb k.1) (B.onb k.1) k.2.1 k.2.2
  let Cr : FVar D X.rank M.rank → SInf D.host.F (Fin M.rank × Fin X.rank) → SInf D.host.F (Fin M.rank × Fin X.rank) :=
    fun k f => ((fockScale D k.1 : ℂ)⁻¹) • (Dr (dir ε M X θ k.1 (um k)) f -
      Complex.I • Dr (dir ε M X θ k.1 (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (um k))) f)
  let Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank) :=
    (MvPolynomial.basisMonomials _ ℂ).constr ℂ fun k => (Multiset.toList (Finsupp.toMultiset k)).foldr Cr g₀
  have hΦ : ∀ Θ : SInf D.host.F (Fin M.rank × Fin X.rank) →ₗ[ℂ] (WO (sgn ε M) X → ℂ),
      (∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f)) →
      Θ ∘ₗ Φ = pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart (frSgn ε A).onb B.onb (Θ g₀) := by
    intro Θ hd
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.comp_apply, pureTensorO, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis, opPow]
    induction (Finsupp.toMultiset k).toList with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih, aPlusAll, Formalism.IndefR.Datum.aPlus, crea, hd, hd, ← map_smul, ← map_sub,
        ← map_smul]
  have hΦ' : ∀ P, Θ (Φ P) = ptF ψ θ (frSgn ε A) B (Θ g₀) P := fun P => LinearMap.congr_fun (hΦ Θ hd) P
  have hsum : ∀ u, At (evI D.host.F) u → ∀ f, Dr u f =
      ∑ t, Dr (dir ε M X θ t (compAt θ t (toO (sgn ε M).gram u))) f := fun u hu f => by
    rw [← hD3 _ _ _ fun t => dir_at hθ t _, ← eq_sum_dir hθ hu]
  have hG : Mo.IsGauss ψ τ g₀ := ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => by
    rw [hD2 u hu _ _ hf, hD2 u' hu' _ _ hf', hsum u hu, hsum u' hu', Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [compAt_cplx hθ A B hc (fun w => by simpa using hrel w) t,
      eq_neg_of_add_eq_zero_left (hg₀ t (compAt θ t (toO (sgn ε M).gram u))), smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]⟩
  have hP : ∀ u, At (evI D.host.F) u → ∀ f ∈ Mo.Pol ψ τ, Dr u f ∈ Mo.Pol ψ τ := fun u hu f hf =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (hD1 u hu f)
  refine ⟨Φ, le_antisymm ?_ (sInf_le ⟨fun f hf => ?_, ?_⟩), fun g' hg' P =>
    LinearMap.congr_fun (hΦ (thL Mo hψ hθ hX hW hM hg') (dRho_thL Mo hψ hθ hX hW hM hD1 hg')) P⟩
  · rw [Module.Basis.constr_range, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    beta_reduce
    induction (Finsupp.toMultiset k).toList with
    | nil => exact Submodule.mem_sInf.2 fun N hN => hN.1 g₀ hG
    | cons i l ih =>
      exact Submodule.smul_mem _ _ (sub_mem (hP _ (dir_at hθ _ _) _ ih) (Submodule.smul_mem _ _ (hP _ (dir_at hθ _ _) _ ih)))
  · obtain ⟨z, rfl⟩ := gauss_line Mo ψ τ hCM hStd h2X h2W f g₀ hG g0 hf
    exact Submodule.smul_mem _ z ⟨1, hi ((hΦ' 1).trans (GlobalTheory.LieScalar.ptF_one _ _ _))⟩
  · rintro u hu _ ⟨P, rfl⟩ f₁ h1
    rw [hD2 u hu _ _ h1, hsum u hu]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨Q, hQ⟩ := dRho_ptF (frSgn ε A) B hψ hθ hv t (compAt θ t (toO (sgn ε M).gram u)) P
    exact ⟨Q, hi (by rw [← hd, hΦ', hΦ', hQ])⟩

end SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.thetaLift_pure_tensor_of_isFinF :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (hd : d = X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X (finCongr hd) Bs Vs Ws M → ∀ (θ : InfFam D), IsInfFam θ →
        ∀ (A : Fr S) (B : Fr X), IsCart ε A B (finCongr hd) Bs Vs Ws →
        ∀ (g : SInf D.host.F (Fin S.rank × Fin d)), g ≠ 0 →
        ∀ (φ₀ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ), (∀ v, φ₀ v ∈ GlobalTheory.WeilM.SB _) →
        (∀ᶠ v in Filter.cofinite, φ₀ v = M.vac v) → (∀ v, φ₀ v ≠ 0) →
        IsFinF ψ θ ε A B (thO M ψ (sgn ε S).gram (finCongr hd) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ₀)) →
        ∃ Φ : PolF D X.rank S.rank →ₗ[ℂ] SInf D.host.F (Fin S.rank × Fin d), LinearMap.range Φ = M.Pol Bs.ψ Bs.emb ∧
          ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
            (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ P,
            thO M ψ (sgn ε S).gram (finCongr hd) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
              fockF ψ θ ε A B (thO M ψ (sgn ε S).gram (finCongr hd) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) P := by
  intro D ψ ε S X d hd Bs Vs Ws M hP θ hθ A B hc g g0 φ₀ hφ hφ' hφ0 hv
  subst hd
  obtain ⟨hBs, hψe, hX, hW, ⟨r, s, hV⟩, ⟨r', s', hWs⟩, hM⟩ := hP
  subst hψe
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hBs.std
  have hF : GlobalTheory.BigNZ.Fam M φ₀ := ⟨hφ, hφ'⟩
  obtain ⟨Φ, h1, h2⟩ := fock_of M hψ hθ A B hBs.cm hBs.std hX hW hM (fun w => (hV.cartan w).1)
    (fun w => (hWs.cartan w).1) hc g g0 (hF.sb hM) (finPart_ne φ₀ hφ0 (hF.std hM)) hv
  refine ⟨Φ, h1, fun φ hs hs' P => ?_⟩
  have hF' : GlobalTheory.BigNZ.Fam M φ := ⟨hs, hs'⟩
  exact h2 _ (hF'.sb hM) P
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsLocalZetaDataRealizingStandardPair
namespace UpperTheory.StandardPairNonvanishing
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdPairLoc GlobalTheory.StdPairCone MeasureTheory
open scoped Matrix

section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

private theorem std_key (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (hν : ν = α / β) (h : GL (Fin (a + a')) k) :
    bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') h =
      smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') h := by
  rw [bigZetaIntegral_eq, smallP]
  obtain ⟨hdet, hrel⟩ := standardPair_frameBlocks_det_and_neg_transpose a a' h
  obtain ⟨hA0, hA⟩ := bigF_stdA ν ϖ c a a' hϖ
  obtain ⟨hB0, hB⟩ := smallF_stdB (k := k) ν ϖ c a a'
  by_cases h0 : (blk₁ (X0 k (finSumFinEquiv (m := a) (n := a')) * (invT h).val)).det = 0
  · have h0' : (blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)).det = 0 := by rw [← hdet, h0, zero_mul]
    rw [hA0 _ h0, hB0 _ h0']; simp
  · have h0' : (blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)).det ≠ 0 := by
      rw [← hdet]; exact mul_ne_zero h0 h.det_ne_zero
    set g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0 with hg₁
    set g₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0' with hg₂
    rw [hA _ g₁ rfl, hB _ g₂ rfl, hrel g₁ g₂ rfl rfl, cball_neg_transpose]
    have hd : gdet g₂ = gdet g₁ * gdet h := Units.ext (by
      simp only [gdet, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, g₁, g₂,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact hdet.symm)
    have hαν : α = ν * β := by rw [hν, div_mul_cancel]
    have e : apow (gdet h) ((Fintype.card (Fin a') : ℂ) / 2) * apow (gdet h) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) =
        apow (gdet h) (-(a : ℂ) / 2) := by
      rw [← apow_add]; congr 1; simp only [Fintype.card_fin]; push_cast; ring
    have e1 : (((ν (gdet g₁ * gdet h))⁻¹ : ℂˣ) : ℂ) = (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) := by
      rw [map_mul, _root_.mul_inv, Units.val_mul]
    have e2 : (α (gdet h) : ℂ) = (ν (gdet h) : ℂ) * (β (gdet h) : ℂ) := by
      rw [hαν, MonoidHom.mul_apply, Units.val_mul]
    have e3 : (ν (gdet h) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hd, e1, apow_mul, e2]
    have key2 : ∀ B V Vi Vhi P1 Pa' PN I : ℂ, V * Vhi = 1 →
        B * (Pa' * PN) * (Vi * P1 * I) = V * B * Pa' * (Vi * Vhi * (P1 * PN) * I) := by
      intro B V Vi Vhi P1 Pa' PN I hV; linear_combination (-(B * Pa' * PN * Vi * P1 * I)) * hV
    rw [← e]
    exact key2 _ _ _ _ _ _ _ _ e3

private theorem stdA_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : stdA ν ϖ c a a' ≠ 0 := by
  intro h
  let X : Matrix (Fin a) (Fin (a + a')) k :=
    Matrix.of fun i j => Fin.addCases (motive := fun _ => k) (fun j => (1 : Matrix (Fin a) (Fin a) k) i j) (fun _ => 0) j
  have e1 : blk₁ X = 1 := by ext i j; simp [X, blk₁]
  have e2 : blk₂ X = 0 := by ext i j; simp [X, blk₂]
  have hX := congrFun h X
  rw [stdA, dite_eq_left] at hX
  · exact Units.ne_zero _ hX
  · rw [e1, e2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

private theorem stdB_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : stdB ν ϖ c a a' ≠ 0 := by
  intro h
  let X : Matrix (Fin a') (Fin (a + a')) k :=
    Matrix.of fun i j => Fin.addCases (motive := fun _ => k) (fun _ => 0) (fun j => (1 : Matrix (Fin a') (Fin a') k) i j) j
  have e1 : blk₁ X = 0 := by ext i j; simp [X, blk₁]
  have e2 : blk₂ X = 1 := by ext i j; simp [X, blk₂]
  have hX := congrFun h X
  rw [stdB, dite_eq_left] at hX
  · exact Units.ne_zero _ hX
  · rw [e1, e2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

end

end UpperTheory.StandardPairNonvanishing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_local_zeta_data_realizing_standard_pair :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
        (Γ : Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') (v : B.P),
        GlobalTheory.LFun.IsHecke F E X.α → GlobalTheory.LFun.IsHecke F E X.β → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsZetaAt B Γ X Rf v → Γ.M.IsGood B.ψ → Γ.M'.IsGood B.ψ → ∀ c : ℕ,
        ∃ ι ι' φ φ', Γ.M.IsLinW B.ψ (B.τ v) (Γ.V.bas v) (Γ.W.bas v) ι ∧ Γ.M'.IsLinBar B.ψ (B.τ v) (Γ.V'.bas v) (Γ.W.bas v) ι' ∧
          ι (Γ.M.vac v) 0 = 1 ∧ ι' (Γ.M'.vac v) 0 = 1 ∧ φ ∈ GlobalTheory.WeilM.SB _ ∧ φ' ∈ GlobalTheory.WeilM.SB _ ∧
          ι φ = GlobalTheory.StdPairCone.stdA (chrW X.ν (B.τ v)) (unifAt v.1) c a a' ∧
          ι' φ' = GlobalTheory.StdPairCone.stdB (chrW X.ν (B.τ v)) (unifAt v.1) c a a' ∧ Rf.p v φ = Rf.p' v φ' ∧ φ ≠ 0 ∧ φ' ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' Γ X Rf v hα hβ hZ _ _ c
  obtain ⟨ι, ι', hι, hι', hv, hv', hz⟩ := hZ
  letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv v.1
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv v.1
  have hν : GlobalTheory.LFun.IsHecke F E X.ν := ⟨hα.1.div' hβ.1, fun x => by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.ν, MonoidHom.div_apply, hα.2, hβ.2, div_one]⟩
  have h1 := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.ν hν v (B.τ v)).2.1
  have hdiv : chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) := by
    ext x
    simp [chrW, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.ν, GlobalTheory.LFun.locChar]
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v.1)).choose_spec
  obtain ⟨sA, sB⟩ := UpperTheory.stdA_stdB_mem_schwartzBruhat (Fv F v) (chrW X.ν (B.τ v)) (unifAt v.1) hϖ h1 c a a'
  obtain ⟨φ, hφ, eφ⟩ := hι.bij.surjOn sA
  obtain ⟨φ', hφ', eφ'⟩ := hι'.bij.surjOn sB
  refine ⟨ι, ι', φ, φ', hι, hι', ?_, ?_, hφ, hφ', eφ, eφ', (hz φ hφ φ' hφ').2 ?_, ?_, ?_⟩
  · rw [hv, Set.indicator_of_mem (by intro i j; exact zero_mem _)]; rfl
  · rw [hv', Set.indicator_of_mem (by intro i j; exact zero_mem _)]; rfl
  · rw [eφ, eφ']
    funext h
    exact UpperTheory.StandardPairNonvanishing.std_key _ _ _ _ c a a' hϖ hdiv h
  · rintro rfl
    exact UpperTheory.StandardPairNonvanishing.stdA_ne _ _ c a a' (by rw [← eφ, map_zero])
  · rintro rfl
    exact UpperTheory.StandardPairNonvanishing.stdB_ne _ _ c a a' (by rw [← eφ', map_zero])
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StageGeo

variable {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))}
  {FA : Fr A} {FA' : Fr A'} {FW : Fr WW} {Bs : Base D.host.F D.host.E} {Γ : Geo D.sp.cm.sig A.rank A'.rank}

structure Reads (α β : T → ((AE D)ˣ →* Circle)) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (Bs : Base D.host.F D.host.E)
    (t : T) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  eα : Xc.α = α t

  eβ : Xc.β = β t

  pl : ∀ w, w ∈ S t ↔ ∃ v : Bs.P, v.1 ∈ Xc.T ∧ splitPrime (Bs.τ v) = w

  unit : ∀ v : Bs.P, v.1 ∈ Xc.T → AUnit (Bs.τ v)

theorem exists_fin (hX : X.Is ψ θ α β νH S) (hG : IsStageGeo ψ X FA FA' FW hX.rank Bs Γ) {t : T}
    {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (hR : Reads α β S Bs t Xc) {om om' R Rf}
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf) {g g'}
    (hg : X.vac = thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g Γ.M.vac))
    (hg' : X.vac' = thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' Γ.M'.vac)) :
    ∃ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ)
      (φ' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ v, φ' v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ v ∉ Xc.T, φ v = Γ.M.vac v) ∧
      (∀ v ∉ Xc.T, φ' v = Γ.M'.vac v) ∧ (∀ v, φ v ≠ 0) ∧ (∀ v, φ' v ≠ 0) ∧ (∀ v ∈ Xc.T, Rf.p v (φ v) = Rf.p' v (φ' v)) ∧
      X.f t = thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) ∧
      X.f' t = thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ') := by
  have hT := hm.triple
  let u : Xc.T → Bs.P := fun v => ⟨v.1, hT.chars.sub v.2⟩
  choose ι ι' φ₀ φ₀' l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 using fun v : Xc.T =>
    UpperTheory.exists_local_zeta_data_realizing_standard_pair _ _ D.sp.cm.sig Bs _ _ Γ Xc Rf (u v) hT.chars.heckeα hT.chars.heckeβ (hm.fin.zeta (u v) v.2) hT.geo.hM hT.geo.hM'
      (X.c t (splitPrime (Bs.τ (u v))))
  have hν : Xc.ν = α t / β t := by rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars.ν, hR.eα, hR.eβ]
  have hψ : Bs.ψ = ψ := hG.pairA.psi
  rw [hν] at l7 l8
  rw [hψ] at l1 l2
  have hS : ∀ w, w ∈ S t ↔ ∃ v : Xc.T, splitPrime (Bs.τ (u v)) = w := fun w =>
    (hR.pl w).trans ⟨fun ⟨v, hv, e⟩ => ⟨⟨v.1, hv⟩, e⟩, fun ⟨v, e⟩ => ⟨u v, v.2, e⟩⟩
  let φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if h : v ∈ Xc.T then φ₀ ⟨v, h⟩ else Γ.M.vac v
  let φ' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if h : v ∈ Xc.T then φ₀' ⟨v, h⟩ else Γ.M'.vac v
  have e1 : ∀ v (h : v ∈ Xc.T), φ v = φ₀ ⟨v, h⟩ := fun v h => dif_pos h
  have e1' : ∀ v (h : v ∈ Xc.T), φ' v = φ₀' ⟨v, h⟩ := fun v h => dif_pos h
  have e2 : ∀ v ∉ Xc.T, φ v = Γ.M.vac v := fun v h => dif_neg h
  have e2' : ∀ v ∉ Xc.T, φ' v = Γ.M'.vac v := fun v h => dif_neg h
  have s1 : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _ ∧ φ v ≠ 0 := fun v => by
    by_cases h : v ∈ Xc.T
    · rw [e1 v h]; exact ⟨l5 _, l10 _⟩
    · rw [e2 v h]; exact ⟨(hT.geo.hM.vac v).1, (hT.geo.hM.vac v).2.1⟩
  have s2 : ∀ v, φ' v ∈ GlobalTheory.WeilM.SB _ ∧ φ' v ≠ 0 := fun v => by
    by_cases h : v ∈ Xc.T
    · rw [e1' v h]; exact ⟨l6 _, l11 _⟩
    · rw [e2' v h]; exact ⟨(hT.geo.hM'.vac v).1, (hT.geo.hM'.vac v).2.1⟩
  refine ⟨φ, φ', fun v => (s1 v).1, fun v => (s2 v).1, e2, e2', fun v => (s1 v).2, fun v => (s2 v).2, fun v h => ?_, ?_, ?_⟩
  · rw [e1 v h, e1' v h]; exact l9 ⟨v, h⟩
  · exact UpperTheory.thetaLift_triple_local_split_places D T A A' WW X ψ θ α β νH S hX hX.rank Bs Γ.V Γ.W Γ.M hG.pairA hG.latA t Xc.T (fun v => Bs.τ (u v)) hS
      (fun v => Γ.V.bas v) (fun v => Γ.W.bas v) ι (fun v => hG.basA (u v)) (fun v => hG.basW (u v) (hR.unit (u v) v.2)) l1 l3 φ
      (fun v => (s1 v).1) e2 (fun v => by rw [e1 v.1 v.2]; exact l7 v) g hg
  · exact UpperTheory.triple_dualCoord_split_places_of_isPair_isLat D T A A' WW X ψ θ α β νH S hX hX.rank Bs Γ.V' Γ.W Γ.M' hG.pairB hG.latB t Xc.T (fun v => Bs.τ (u v)) hS
      (fun v => Γ.V'.bas v) (fun v => Γ.W.bas v) ι' (fun v => hG.basB (u v)) (fun v => hG.basW (u v) (hR.unit (u v) v.2)) l2 l4 φ'
      (fun v => (s2 v).1) e2' (fun v => by rw [e1' v.1 v.2]; exact l8 v) g' hg'

theorem exists_vac {ε : Bool} {S₀ : HSp D} {d : ℕ} {e : Fin d ≃ Fin WW.rank} {Vs : Spc D.host.F D.host.E S₀.rank}
    {Ws : Spc D.host.F D.host.E d} {M : Model D.sp.cm.sig Vs Ws} (hP : IsPair ψ ε S₀ WW e Bs Vs Ws M)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S₀.rank → D.host.E)} {ΛX : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)}
    (hL : IsLat e Vs Ws ΛS ΛX) {s s'} {f : WO (sgn ε S₀) WW → ℂ} (hf : IsVacO ψ θ (sgn ε S₀) WW s s' ΛS ΛX f) :
    ∃ g : SInf D.host.F (Fin S₀.rank × Fin d), g ≠ 0 ∧ f = thO M ψ (sgn ε S₀).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) := by
  obtain ⟨g, hg⟩ := UpperTheory.exists_thO_eq_of_isLatVac_thetaFun D ψ ε S₀ WW d e Bs Vs Ws M hP ΛS ΛX hL f hf.2.theta hf.2.lat
  refine ⟨g, fun h0 => ?_, hg⟩
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have h1 := hn p hp
  have h2 : f = 0 := by
    rw [hg, h0]
    funext x
    simp [thO, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  rw [h2] at h1
  simp [nrm2] at h1

end GlobalTheory.StageGeo

end
