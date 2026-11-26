module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RatKDeg
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolKerStd
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualFourfoldCurveIdealLattice
public import Formalism.LocalToGlobal.Columns.ChainOneOk
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZeroAlt
public import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.SymLevEnt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPAmbOfTiesD
open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

namespace TE

section PullD

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem map_jetMap' {L : Type} [Field L] (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    MvPolynomial.map σ (jetMap J n P) = jetMap (fun m => σ (J m)) n (MvPolynomial.map σ P) := by
  rw [Shape.map_jetMap]
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]

theorem jetMap_pullD (σ : K →+* ℂ) (cD : ι → ℂ) (G : VCx ι a b → ℂ) (hG : ContDiff ℂ ⊤ G)
    (g : ι → Matrix (Fin a) (Fin a) K) (h : ι → Matrix (Fin b) (Fin b) K) (L : VCx ι a b →ₗ[ℂ] VCx ι a b)
    (hL : ∀ k : DVar ι a b, L (coordX k) =
      ∑ p : Fin b × Fin a, (σ (h k.1 p.1 k.2.1) * σ (g k.1 k.2.2 p.2)) • coordX ((k.1, p.1, p.2) : DVar ι a b))
    (lam : ι → DomWeight a) (n : ι → ℕ)
    (J J' : (DVar ι a b →₀ ℕ) → K) (κ κ' : ℂ) (hJ : ∀ m, (∀ τ, degAt m τ = opDeg lam n τ) → σ (J m) = κ * jetC cD G m)
    (hJ' : ∀ m, (∀ τ, degAt m τ = opDeg lam n τ) → σ (J' m) = κ' * jetC cD (fun z => G (L z)) m) (r : K) (hr : κ' = σ r * κ)
    (P : Pol K ι a) (hP : P ∈ DIV.VV K lam) (hgP : Formalism.GradedWeylDivisibility.blockAct K g P ∈ DIV.VV K lam) :
    jetMap J' n P = (r * ∏ τ, (g τ).det ^ n τ) • Formalism.GradedWeylDivisibility.blockAct K h (jetMap J n (Formalism.GradedWeylDivisibility.blockAct K g P)) := by
  apply MvPolynomial.map_injective σ σ.injective
  have hc := jetMap_pull (RingHom.id ℂ) cD G hG (fun τ => (g τ).map σ) (fun τ => (h τ).map σ) L (fun k => hL k)
    (fun m => κ * jetC cD G m) (fun m => κ' * jetC cD (fun z => G (L z)) m) κ κ' (fun m => rfl) (fun m => rfl) (σ r) hr n
    (MvPolynomial.map σ P)
  have e1 : jetMap (fun m => σ (J' m)) n (MvPolynomial.map σ P) = jetMap (fun m => κ' * jetC cD (fun z => G (L z)) m) n (MvPolynomial.map σ P) :=
    jet_local_rationality ℂ ι a b lam n _ _ hJ' _ (map_mem_VV σ lam P hP)
  have e2 : jetMap (fun m => σ (J m)) n (MvPolynomial.map σ (Formalism.GradedWeylDivisibility.blockAct K g P)) =
      jetMap (fun m => κ * jetC cD G m) n (MvPolynomial.map σ (Formalism.GradedWeylDivisibility.blockAct K g P)) :=
    jet_local_rationality ℂ ι a b lam n _ _ hJ _ (map_mem_VV σ lam _ hgP)
  have hR : MvPolynomial.map σ ((r * ∏ τ, (g τ).det ^ n τ) • Formalism.GradedWeylDivisibility.blockAct K h (jetMap J n (Formalism.GradedWeylDivisibility.blockAct K g P))) =
      (σ r * ∏ τ, ((g τ).map σ).det ^ n τ) • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (h τ).map σ)
        (jetMap (fun m => κ * jetC cD G m) n (Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (g τ).map σ) (MvPolynomial.map σ P))) := by
    rw [smul_eq_C_mul, map_mul, map_C, map_blockAct, map_jetMap', e2, map_blockAct, C_mul']
    congr 1
    rw [map_mul, map_prod]
    simp only [map_pow, RingHom.map_det]
    rfl
  rw [map_jetMap', e1, hc, hR]

end PullD

end TE

section MainD

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem thEquivP_ofD (e : X.Tau → ℤ) (hV : JetInVV X.K lam lam' n) (hrat : A.JetsRatDeg a b Sall D (opDeg lam n)) (hAn : A.IndOmega a b Sall D)
    (hInd : A.ThIndEq a b Sall D) (hChi : A.ChiLaw a b) (hMa : MuProdLaw a sel SB mU mI e) (hMb : MuProdLaw b sel SB mU mI e)
    (hW : WtLaw lam lam' n e) :
    ThEquivP (thDistC A Sall SB D sel mU mI lam lam' n) Sall D ((rhoVr X.emb lam).comp (ufGL X.E a)) ((rhoVr X.emb lam').comp (ufGL X.E b)) := by
  intro γ γ' N fr N' fr' c x hR
  have hR' : InRange Sall D c (gmap γ.1 N) (gmap γ'.1 N') (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) :=
    ⟨isSdLat_gmap hR.1 γ, isSdLat_gmap hR.2.1 γ', hR.2.2.1, hR.2.2.2.1, (divLat_gmap_iff Sall D γ.1 γ'.1 N N' x).2 hR.2.2.2.2⟩
  unfold thDistC
  rw [if_pos ⟨hR'.2.2.2.1, hR'.2.2.2.2⟩, if_pos ⟨hR.2.2.2.1, hR.2.2.2.2⟩]
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  obtain ⟨d, hd⟩ : ∃ d : X.Tau → X.K, d = fun τ => X.emb τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d' : X.Tau → X.K, d' = fun τ => X.emb τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) := ⟨_, rfl⟩
  have hdτ : ∀ τ, X.emb τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = d τ := fun τ => by rw [hd]
  have hdτ' : ∀ τ, X.emb τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) = d' τ := fun τ => by rw [hd']
  have hd0 : ∀ τ, d τ ≠ 0 := fun τ => by rw [← hdτ]; exact (map_ne_zero (X.emb τ)).2 (Units.ne_zero _)
  have hd0' : ∀ τ, d' τ ≠ 0 := fun τ => by rw [← hdτ']; exact (map_ne_zero (X.emb τ)).2 (Units.ne_zero _)
  have hinv : ∀ τ, X.emb τ ((LinearEquiv.det (γ⁻¹ : UF X.E a).1 : X.Eˣ) : X.E) = (d τ)⁻¹ := by
    intro τ
    rw [← hdτ, InvMemClass.coe_inv, map_inv, Units.val_inv_eq_inv_val, map_inv₀]
  have hgP : Formalism.GradedWeylDivisibility.blockAct X.K (TE.matT X.emb γ) (P : Pol X.K X.Tau a) ∈ DIV.VV X.K lam := by
    have hm := (((rhoVr X.emb lam).comp (ufGL X.E a)) γ⁻¹ P).2
    rw [TE.rho_coe, inv_inv] at hm
    have hne : (∏ τ, (X.emb τ ((LinearEquiv.det (γ⁻¹ : UF X.E a).1 : X.Eˣ) : X.E)) ^ (-(lam τ).detShift)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((map_ne_zero (X.emb τ)).2 (Units.ne_zero _))
    have h2 := (DIV.VV X.K lam).smul_mem (∏ τ, (X.emb τ ((LinearEquiv.det (γ⁻¹ : UF X.E a).1 : X.Eˣ) : X.E)) ^ (-(lam τ).detShift))⁻¹ hm
    rwa [inv_smul_smul₀ hne] at h2
  have hpull := TE.jetMap_pullD A.σ₀ A.cD (A.thInd Sall N N' c x) (hAn N N' c x hR) (TE.matT X.emb γ) (TE.matT X.emb γ'⁻¹)
    (TE.mulL (fun τ => (TE.matT X.emb γ'⁻¹ τ).map A.σ₀) (fun τ => (TE.matT X.emb γ τ).map A.σ₀))
    (fun k => TE.mulL_coordX _ _ k) lam n
    (A.jetK Sall N N' c x) (A.jetK Sall (gmap γ.1 N) (gmap γ'.1 N') c (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap))
    (A.chiF a b N N')⁻¹ (A.chiF a b (gmap γ.1 N) (gmap γ'.1 N'))⁻¹ (fun m hm => jetK_spec_deg A Sall D _ hrat N N' c x hR m hm)
    (by
      intro m hm
      rw [jetK_spec_deg A Sall D _ hrat _ _ c _ hR' m hm]
      congr 2
      funext z
      rw [hInd γ γ' N N' c x hR z, pullV_eq])
    ((∏ τ, d τ) ^ ((b / 2 : ℕ) : ℤ) * (∏ τ, d' τ) ^ (-((a / 2 : ℕ) : ℤ)))
    (by
      rw [hChi γ γ' N N' hR.1 hR.2.1, mul_inv, mul_inv, ← zpow_neg, neg_neg, ← zpow_neg, map_mul, map_zpow₀, map_zpow₀, map_prod, map_prod]
      simp only [hd, hd']
      rfl)
    (P : Pol X.K X.Tau a) P.2 hgP
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, Submodule.coe_smul,
    Submodule.coe_smul, jetOp_coe lam lam' n hV, TE.rho_coe, jetOp_coe lam lam' n hV, TE.rho_coe, inv_inv, hpull,
    hMa γ N fr hR.1, hMb γ' N' fr' hR.2.1]
  simp only [map_smul, smul_smul, TE.det_matT, hinv, hdτ, hdτ']
  congr 1
  have A1 := scal_a d hd0 e (fun τ => (lam τ).detShift) n (b / 2) hW.1
  have A2 := scal_b d' hd0' e (fun τ => (lam' τ).detShift) (a / 2) hW.2
  rw [← A1, ← A2, mul_inv]
  ring

end MainD

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word)

theorem thEquivP_stepT_ofD {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ) (he : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩)
    (hrat : A.JetsRatDeg (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i))
    (hE : A.EOmega (R.N i) (R.N (i + 1)))
    (hInd : A.ThIndEq (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (hChi : A.ChiLaw (R.N i) (R.N (i + 1)))
    (hMa : MuProdLaw (R.N i) sel (rowSG Pr sel mu) (mUof Ch mu i) (muAtT Ch sel mu cst i) e)
    (hMb : MuProdLaw (R.N (i + 1)) sel (rowSG Pr sel mu) (mUof Ch mu i) (muAtT Ch sel mu cst i) e) :
    ThEquivP (stepT W Ch sel mu cst A u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho :=
  thEquivP_ofD A (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst * cBof sel mu cst u) sel (mUof Ch mu i) (muAtT Ch sel mu cst i)
    (W.lamTrue u i) (W.lamTrue u (i + 1)) (nuLast W u i) e (jet_in_weight_space_chain W u hi) hrat (indOmega_of A _ _ _ _ hE) hInd hChi hMa hMb
    (wtLaw_step W u hi e he)

theorem chThT_laws_of {m2 : ℕ} (hm : R.m = m2 + 2)
    (h : ∀ i, i < R.m → ThEquivP (stepT W Ch sel mu cst A u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho) :
    (∀ i, i ≤ m2 → ThEquivP ((chThT W Ch sel mu cst A u m2).th i) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho) ∧
    ThEquivP (chThT W Ch sel mu cst A u m2).top (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho :=
  ⟨fun i hi => h i (by omega), (top_cast W Ch sel mu cst A u hm).1.2 (h (m2 + 1) (by omega))⟩

end Chain

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m} (u : Pr.Word)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem thEquivP_ambOf_tiesD (hIT : ThIndOfEq) {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) (hT : LawTies W Ch sel mu cst G) (hTu : 0 < Pr.T u) {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ)
    (he : ∀ τ, (e τ : ℚ) = (W.row τ).e ⟨i, hi⟩)
    (hLa : (ambOf s B χ cD : Amb X).LaHyp (R.N i) (R.N (i + 1)) (Sall sel mu u))
    (hrat : (ambOf s B χ cD : Amb X).JetsRatDeg (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i)) :
    ThEquivP (stepT W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho := by
  have he' : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩ := by
    intro τ
    rw [he τ, ← hT.2.2.2 u τ]
    rfl
  exact thEquivP_stepT_ofD W Ch sel mu cst (ambOf s B χ cD) u hi e he' hrat (eOmega_ambOf s B χ cD hN _ _)
    (thIndEq_ambOf_of s B χ cD hIT hN (even_rankN R i) (even_rankN R (i + 1)) _ (modulus_pos sel mu cst u hTu) hLa)
    (chiLaw_ambOf s B χ cD hN (even_rankN R i) (even_rankN R (i + 1)))
    (muProdLaw_of hX hPr hsel hg hT i hi e he _) (muProdLaw_of hX hPr hsel hg hT i hi e he _)

end Rec

end Formalism.L2.Ker
end
end

section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.HermitianHalfLattice.MLConjTranspose
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.TI

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.Th1.H (IsIsom imgLat)

section Mat

variable {E : Type} [Field E] {ι : Type} (emb : ι → E →+* ℂ)

def mL {n m : ℕ} (f : Sp E n →ₗ[E] Sp E m) (τ : ι) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i k => emb τ (f (Pi.single k 1) i)

theorem mL_apply {n m : ℕ} (f : Sp E n →ₗ[E] Sp E m) (τ : ι) (i : Fin m) (k : Fin n) :
    mL emb f τ i k = emb τ (f (Pi.single k 1) i) := rfl

theorem lin_apply_eq_sum {n m : ℕ} (f : Sp E n →ₗ[E] Sp E m) (v : Sp E n) (i : Fin m) :
    f v i = ∑ k, v k * f (Pi.single k 1) i := by
  classical
  have h := LinearMap.pi_apply_eq_sum_univ f v
  have e : ∀ k : Fin n, (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := by
    intro k; funext j; simp [Pi.single_apply, eq_comm]
  rw [h, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e k, Pi.smul_apply, smul_eq_mul]

theorem mL_comp {n m l : ℕ} (f : Sp E m →ₗ[E] Sp E l) (g : Sp E n →ₗ[E] Sp E m) (τ : ι) :
    mL emb (f ∘ₗ g) τ = mL emb f τ * mL emb g τ := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, mL_apply, LinearMap.comp_apply, lin_apply_eq_sum f (g (Pi.single j 1)) i, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, mul_comm]
  rfl

theorem mL_id {n : ℕ} (τ : ι) : mL emb (LinearMap.id : Sp E n →ₗ[E] Sp E n) τ = 1 := by
  classical
  ext i j
  rw [mL_apply, LinearMap.id_apply, Matrix.one_apply, Pi.single_apply]
  split_ifs <;> simp

theorem mL_equiv {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (τ : ι) : mL emb g.toLinearMap τ * mL emb g.symm.toLinearMap τ = 1 := by
  rw [← mL_comp]
  have : g.toLinearMap ∘ₗ g.symm.toLinearMap = LinearMap.id := by ext v i; simp
  rw [this, mL_id]

theorem mL_equiv' {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (τ : ι) : mL emb g.symm.toLinearMap τ * mL emb g.toLinearMap τ = 1 := by
  rw [← mL_comp]
  have : g.symm.toLinearMap ∘ₗ g.toLinearMap = LinearMap.id := by ext v i; simp
  rw [this, mL_id]

end Mat

section Unit

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} (emb : ι → E →+* ℂ)

theorem mL_conjTranspose (hst : ∀ τ x, emb τ (star x) = star (emb τ x)) {n : ℕ} (γ : UF E n) (τ : ι) :
    (mL emb γ.1.toLinearMap τ).conjTranspose = mL emb γ.1.symm.toLinearMap τ := by
  ext i k
  rw [Matrix.conjTranspose_apply, mL_apply, mL_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, TE.ufInv_apply γ i k, hst]

end Unit

section RVdef

variable {X : Fields} (A : Amb X) {a b : ℕ}

abbrev zM (z : VCx X.Tau a b) (τ : X.Tau) : Matrix (Fin b) (Fin a) ℂ := Matrix.of (z τ)

def mulM (h : X.Tau → Matrix (Fin b) (Fin b) ℂ) (g : X.Tau → Matrix (Fin a) (Fin a) ℂ) (z : VCx X.Tau a b) : VCx X.Tau a b :=
  fun τ => Matrix.of.symm (h τ * zM z τ * g τ)

theorem zM_mulM (h : X.Tau → Matrix (Fin b) (Fin b) ℂ) (g : X.Tau → Matrix (Fin a) (Fin a) ℂ) (z : VCx X.Tau a b) (τ : X.Tau) :
    zM (mulM h g z) τ = h τ * zM z τ * g τ := by
  ext i j
  rfl

theorem mulM_apply (h : X.Tau → Matrix (Fin b) (Fin b) ℂ) (g : X.Tau → Matrix (Fin a) (Fin a) ℂ) (z : VCx X.Tau a b) (τ : X.Tau) (i : Fin b) (j : Fin a) :
    mulM h g z τ i j = (h τ * zM z τ * g τ) i j := rfl

theorem mulM_mulM (h h' : X.Tau → Matrix (Fin b) (Fin b) ℂ) (g g' : X.Tau → Matrix (Fin a) (Fin a) ℂ) (z : VCx X.Tau a b) :
    mulM h g (mulM h' g' z) = mulM (fun τ => h τ * h' τ) (fun τ => g' τ * g τ) z := by
  funext τ
  simp only [mulM, zM_mulM, Matrix.mul_assoc]

theorem mulM_one (z : VCx X.Tau a b) : mulM (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) z = z := by
  funext τ
  simp [mulM, zM]

def RV (γ : UF X.E a) (γ' : UF X.E b) : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b where
  toFun := mulM (mL (X.embC A.σ₀) γ'.1.toLinearMap) (mL (X.embC A.σ₀) γ.1.symm.toLinearMap)
  invFun := mulM (mL (X.embC A.σ₀) γ'.1.symm.toLinearMap) (mL (X.embC A.σ₀) γ.1.toLinearMap)
  map_add' z w := by
    funext τ i j
    rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, mulM_apply, mulM_apply, mulM_apply]
    have e : zM (z + w) τ = zM z τ + zM w τ := rfl
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' c z := by
    funext τ i j
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, mulM_apply, mulM_apply, RingHom.id_apply]
    have e : zM (c • z) τ = c • zM z τ := rfl
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
  left_inv z := by
    show mulM _ _ (mulM _ _ z) = z
    rw [mulM_mulM]
    simp only [mL_equiv']
    exact mulM_one z
  right_inv z := by
    show mulM _ _ (mulM _ _ z) = z
    rw [mulM_mulM]
    simp only [mL_equiv]
    exact mulM_one z

theorem RV_apply (γ : UF X.E a) (γ' : UF X.E b) (z : VCx X.Tau a b) :
    RV A γ γ' z = mulM (mL (X.embC A.σ₀) γ'.1.toLinearMap) (mL (X.embC A.σ₀) γ.1.symm.toLinearMap) z := rfl

theorem RV_symm_apply (γ : UF X.E a) (γ' : UF X.E b) (z : VCx X.Tau a b) : (RV A γ γ').symm z = A.pullV a b γ.1 γ'.1 z := by
  show mulM _ _ z = _
  funext τ i j
  simp only [mulM, zM, Amb.pullV, Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply, mL_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem RV_embH (γ : UF X.E a) (γ' : UF X.E b) (y : HomE X.E a b) :
    RV A γ γ' (embH (X.embC A.σ₀) A.δ y) = embH (X.embC A.σ₀) A.δ (γ'.1.toLinearMap ∘ₗ y ∘ₗ γ.1.symm.toLinearMap) := by
  have e : ∀ τ, zM (embH (X.embC A.σ₀) A.δ y) τ = A.δ • mL (X.embC A.σ₀) y τ := by
    intro τ; ext i j; simp [zM, embH, mL_apply]
  funext τ i j
  rw [RV_apply, mulM_apply, e, Matrix.mul_smul, Matrix.smul_mul, ← mL_comp, ← mL_comp, Matrix.smul_apply, mL_apply, smul_eq_mul]
  rfl

end RVdef

section Iso

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem HV_eq_trace (sc : ℝ) (z w : VCx X.Tau a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, (zM z τ * (zM w τ).conjTranspose).trace := by
  show (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = _
  congr 1

theorem isIsom_RV (hst : ∀ τ x, X.embC A.σ₀ τ (star x) = star (X.embC A.σ₀ τ x)) (γ : UF X.E a) (γ' : UF X.E b) :
    IsIsom (HV A.sc) (HV A.sc) (RV A γ γ' : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) := by
  intro z w
  show HV A.sc (RV A γ γ' z) (RV A γ γ' w) = HV A.sc z w
  rw [HV_eq_trace, HV_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [RV_apply, zM_mulM, Matrix.conjTranspose_mul]
  set P := mL (X.embC A.σ₀) γ'.1.toLinearMap τ
  set Q := mL (X.embC A.σ₀) γ.1.symm.toLinearMap τ
  have hP : P.conjTranspose * P = 1 := by
    rw [mL_conjTranspose _ hst γ' τ]; exact mL_equiv' _ γ'.1 τ
  have hQ : Q * Q.conjTranspose = 1 := by
    have h1 := mL_conjTranspose _ hst γ τ
    have h2 : Q.conjTranspose = mL (X.embC A.σ₀) γ.1.toLinearMap τ := by
      show (mL (X.embC A.σ₀) γ.1.symm.toLinearMap τ).conjTranspose = _
      rw [← h1, Matrix.conjTranspose_conjTranspose]
    rw [h2]; exact mL_equiv' _ γ.1 τ
  calc (P * zM z τ * Q * (Q.conjTranspose * ((zM w τ).conjTranspose * P.conjTranspose))).trace
      = (P * (zM z τ * (Q * Q.conjTranspose) * (zM w τ).conjTranspose) * P.conjTranspose).trace := by
        simp only [Matrix.mul_assoc]
    _ = (P.conjTranspose * P * (zM z τ * (zM w τ).conjTranspose)).trace := by
        rw [hQ, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = (zM z τ * (zM w τ).conjTranspose).trace := by rw [hP, Matrix.one_mul]

theorem alV_RV (hst : ∀ τ x, X.embC A.σ₀ τ (star x) = star (X.embC A.σ₀ τ x)) (γ : UF X.E a) (γ' : UF X.E b) (z : VCx X.Tau a b) :
    alV A.d A.sc (RV A γ γ' z) = alV A.d A.sc z := by
  unfold alV Formalism.L2.Th1.H.alphaQ Formalism.L2.Th1.H.qOf
  rw [show HV A.sc (RV A γ γ' z) (RV A γ γ' z) = HV A.sc z z from isIsom_RV A hst γ γ' z z]

theorem imgLat_laV (γ : UF X.E a) (γ' : UF X.E b) (M M' : Submodule (𝓞 X.E) (HomE X.E a b))
    (h : ∀ y, y ∈ M' ↔ γ'.1.symm.toLinearMap ∘ₗ y ∘ₗ γ.1.toLinearMap ∈ M) :
    imgLat (RV A γ γ' : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (laV (X.embC A.σ₀) A.δ M) = laV (X.embC A.σ₀) A.δ M' := by
  ext v
  simp only [imgLat, laV, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
  constructor
  · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨γ'.1.toLinearMap ∘ₗ y ∘ₗ γ.1.symm.toLinearMap, (h _).2 ?_, ?_⟩
    · have e : γ'.1.symm.toLinearMap ∘ₗ (γ'.1.toLinearMap ∘ₗ y ∘ₗ γ.1.symm.toLinearMap) ∘ₗ γ.1.toLinearMap = y := by
        ext v i; simp
      rw [e]; exact hy
    · exact (RV_embH A γ γ' y).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨embH (X.embC A.σ₀) A.δ (γ'.1.symm.toLinearMap ∘ₗ y ∘ₗ γ.1.toLinearMap), ⟨_, (h y).1 hy, rfl⟩, ?_⟩
    show RV A γ γ' _ = _
    rw [RV_embH]
    congr 1
    ext v i; simp

end Iso

end Formalism.L2.Ker.TI
end
end

section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.HermitianHalfLattice.MemHalfBOEquiv
section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.HermitianHalfLattice.ConjHSymmApply
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.TI

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

variable {E : Type} [Field E] {a b : ℕ}

def conjH (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b ≃ₗ[E] HomE E a b where
  toFun y := γ'.toLinearMap ∘ₗ y ∘ₗ γ.symm.toLinearMap
  invFun y := γ'.symm.toLinearMap ∘ₗ y ∘ₗ γ.toLinearMap
  map_add' y y' := by ext v i; simp
  map_smul' r y := by ext v i; simp
  left_inv y := by ext v i; simp
  right_inv y := by ext v i; simp

theorem conjH_symm_apply (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (y : HomE E a b) :
    (conjH γ γ').symm y = γ'.symm.toLinearMap ∘ₗ y ∘ₗ γ.toLinearMap := rfl

end Formalism.L2.Ker.TI
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.TI

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem equiv_osmulW (φ : W ≃ₗ[E] W) (r : 𝓞 E) (x : W) : φ (r • x) = r • φ x := by
  rw [← algebraMap_smul E r x, map_smul, algebraMap_smul]

theorem mem_localization_equiv (φ : W ≃ₗ[E] W) {M M' : Submodule (𝓞 E) W} (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M)
    (Q : HeightOneSpectrum (𝓞 E)) (y : W) : y ∈ localization₂ Q.asIdeal M' ↔ φ.symm y ∈ localization₂ Q.asIdeal M := by
  rw [mem_locP, mem_locP]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [← equiv_osmulW]
    exact (hM _).1 h
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, (hM _).2 ?_⟩
    rw [equiv_osmulW]
    exact h

theorem mem_twO_equiv (φ : W ≃ₗ[E] W) {M M' : Submodule (𝓞 E) W} (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M)
    (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : W) : y ∈ twist₂ M' c e ↔ φ.symm y ∈ twist₂ M c e := by
  rw [mem_twO, mem_twO]
  refine forall_congr' fun Q => ?_
  rw [mem_localization_equiv φ hM Q, map_smul]

theorem mem_halfAO_equiv {a b : ℕ} (φ : HomE E a b ≃ₗ[E] HomE E a b) {M M' : Submodule (𝓞 E) (HomE E a b)}
    (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M) (SS : Finset (HeightOneSpectrum (𝓞 E))) (c : ℕ) (y : HomE E a b) :
    y ∈ halfAO SS M' c ↔ φ.symm y ∈ halfAO SS M c :=
  mem_twO_equiv φ hM c _ y

theorem mem_halfBO_equiv {a b : ℕ} (φ : HomE E a b ≃ₗ[E] HomE E a b) {M M' : Submodule (𝓞 E) (HomE E a b)}
    (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M) (SS : Finset (HeightOneSpectrum (𝓞 E))) (c : ℕ) (y : HomE E a b) :
    y ∈ halfBO SS M' c ↔ φ.symm y ∈ halfBO SS M c :=
  mem_twO_equiv φ hM c _ y

theorem mem_mulLat_equiv (φ : W ≃ₗ[E] W) {M M' : Submodule (𝓞 E) W} (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M)
    (c : ℕ) (y : W) : y ∈ mulLat c M' ↔ φ.symm y ∈ mulLat c M := by
  simp only [mulLat, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨φ.symm z, (hM z).1 hz, by rw [equiv_osmulW]⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨φ z, (hM _).2 (by simpa using hz), ?_⟩
    rw [← equiv_osmulW, hzy, LinearEquiv.apply_symm_apply]

end Gen

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homO_gmap (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (y : HomE E a b) : y ∈ homO (gmap γ N) (gmap γ' N') ↔ (conjH γ γ').symm y ∈ homO N N' := by
  change (∀ v ∈ gmap γ N, y v ∈ gmap γ' N') ↔ ∀ u ∈ N, ((conjH γ γ').symm y) u ∈ N'
  constructor
  · intro h u hu
    have := h (γ u) ((mem_gmap γ N _).2 (by simpa using hu))
    rw [mem_gmap] at this
    simpa [conjH_symm_apply] using this
  · intro h v hv
    rw [mem_gmap]
    have := h (γ.symm v) ((mem_gmap γ N v).1 hv)
    simpa [conjH_symm_apply] using this

theorem mem_perO_gmap (AA : Submodule (𝓞 E) E) (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (y : HomE E a b) : y ∈ perO AA (gmap γ N) (gmap γ' N') ↔ (conjH γ γ').symm y ∈ perO AA N N' := by
  have key : perO AA (gmap γ N) (gmap γ' N') = (perO AA N N').map (conjE γ γ' : HomE E a b →ₗ[𝓞 E] HomE E a b) := by
    unfold perO
    rw [Submodule.map_span]
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨r, hr, x, hx, rfl⟩
      refine ⟨r • (conjE γ γ').symm x, ⟨r, hr, _, (mem_homO_gmap γ γ' N N' x).1 hx, rfl⟩, ?_⟩
      show conjH γ γ' (r • (conjH γ γ').symm x) = r • x
      rw [map_smul, LinearEquiv.apply_symm_apply]
    · rintro ⟨w, ⟨r, hr, x, hx, rfl⟩, rfl⟩
      refine ⟨r, hr, conjE γ γ' x, (mem_homO_gmap γ γ' N N' _).2 ?_, ?_⟩
      · show (conjH γ γ').symm (conjH γ γ' x) ∈ homO N N'
        rw [LinearEquiv.symm_apply_apply]; exact hx
      · show conjH γ γ' (r • x) = r • conjH γ γ' x
        rw [map_smul]
  rw [key, Submodule.mem_map_equiv]
  rfl

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (y : HomE E a b) :
    y ∈ homAt S (gmap γ N) (gmap γ' N') ↔ (conjH γ γ').symm y ∈ homAt S N N' := by
  rw [homAt_gmap, Submodule.mem_map_equiv]
  rfl

end Lat

section Lift

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem isLift_conj (S : Finset (HeightOneSpectrum (𝓞 X.E))) (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x s' : HomE X.E a b)
    (h : A.IsLift S (gmap γ N) (gmap γ' N') c (conjH γ γ' x) s') : A.IsLift S N N' c x ((conjH γ γ').symm s') := by
  obtain ⟨⟨c', hc', hs⟩, hx⟩ := h
  refine ⟨⟨c', hc', (mem_halfAO_equiv (conjH γ γ') (mem_perO_gmap A.AA γ γ' N N') S c' s').1 hs⟩, ?_⟩
  have := (mem_mulLat_equiv (conjH γ γ') (mem_homAt_gmap S γ γ' N N') c _).1 hx
  rwa [map_sub, LinearEquiv.symm_apply_apply] at this

end Lift

end Formalism.L2.Ker.TI
end
end

section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkThindEq
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section SlopeTestRemainingChoices

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sumU_eq_inter {H : Sesq V} {α : V → ℂ} {Λ₁ Λ₂ : AddSubgroup V} {F : V → ℂ} {S : Finset V} (hH : IsHerm H)
    (hS : IsSemiChar H Λ₂ α) (hF : F ∈ fixedBy H α Λ₁) (hSr : IsReps Λ₁ Λ₂ S) (hidx : relIdx Λ₁ Λ₂ ≠ 0) (z : V) :
    sumU H α S F z = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ) * inter H α Λ₁ Λ₂ F z := by
  rw [Formalism.L2.Th1.H.interReps V H hH Λ₁ Λ₂ α hS F hF S hSr z]
  have h3 : ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx))).ne'
  field_simp

end SlopeTestRemainingChoices

section Lift

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem homE_zero_of_aa_bot (hLa : A.LaHyp a b S) (hN : IsSdLat N) (hN' : IsSdLat N') (h : A.AA = ⊥) (f : HomE X.E a b) : f = 0 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · refine LinearMap.ext fun v => ?_
    have hv : v = 0 := funext fun i => (Fin.cast ha i).elim0
    rw [hv, map_zero, LinearMap.zero_apply]
  rcases Nat.eq_zero_or_pos b with hb | hb
  · exact LinearMap.ext fun v => funext fun i => (Fin.cast hb i).elim0
  exfalso
  have hsd := ((hLa.2.2.2.2.2 N N' hN hN').2).1
  obtain ⟨τ⟩ := hLa.2.1
  have hL : LamC (X.embC A.σ₀) A.δ A.AA N N' = ⊥ := by
    unfold LamC laV; rw [h, perO_bot]; simp
  rw [hL] at hsd
  have hv : (show VCx X.Tau a b from fun _ _ _ => (1 : ℂ)) ∈ dualLat (HV A.sc) (⊥ : AddSubgroup (VCx X.Tau a b)) := by
    intro y hy
    rw [AddSubgroup.mem_bot] at hy
    exact ⟨0, by simp [hy, altE]⟩
  unfold IsSelfDual at hsd
  rw [hsd, AddSubgroup.mem_bot] at hv
  have := congrFun (congrFun (congrFun hv τ) ⟨0, hb⟩) ⟨0, ha⟩
  simp at this

theorem exists_isLift (hLa : A.LaHyp a b S) (hN : IsSdLat N) (hN' : IsSdLat N') {c D : ℕ} (hD : 0 < D) (hcD : c ∣ D) {x : HomE X.E a b}
    (hx : x ∈ divLat D (homAt S N N')) : ∃ s, A.IsLift S N N' c x s := by
  by_cases hAA0 : A.AA = ⊥
  · refine ⟨0, ⟨⟨1, one_pos, zero_mem _⟩, ?_⟩⟩
    rw [homE_zero_of_aa_bot A S N N' hLa hN hN' hAA0 x, sub_zero]
    exact zero_mem _
  · obtain ⟨s, hs⟩ := lf_exists_liftS A S hLa.2.2.2.1 hAA0 N N' hN hN' hD hx
    exact ⟨s, lf_isLift_of_liftS A S hLa.2.2.2.1 N N' hD hcD hs⟩

end Lift

theorem theta_coset_indicator_natural : ThIndOfEq := by
  intro X A a b Sall D hst hD hLa hEq
  unfold Amb.ThIndEq
  intro γ γ' N N' c x hR z
  obtain ⟨hN, hN', hc, hcD, hx⟩ := hR
  obtain ⟨w, rfl⟩ := (TI.RV A γ γ').surjective z
  have hgN : IsSdLat (gmap γ.1 N) := isSdLat_gmap hN γ
  have hgN' : IsSdLat (gmap γ'.1 N') := isSdLat_gmap hN' γ'
  have hpull : ∀ v, A.pullV a b γ.1 γ'.1 ((TI.RV A γ γ') v) = v := fun v => by
    rw [← TI.RV_symm_apply, LinearEquiv.symm_apply_apply]

  have hx' : γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap ∈ divLat D (homAt Sall (gmap γ.1 N) (gmap γ'.1 N')) := by
    show ((D : 𝓞 X.E) • (LinearMap.id : HomE X.E a b →ₗ[𝓞 X.E] HomE X.E a b)) (TI.conjH γ.1 γ'.1 x) ∈ homAt Sall (gmap γ.1 N) (gmap γ'.1 N')
    rw [TI.mem_homAt_gmap, LinearMap.smul_apply, LinearMap.id_apply, TI.equiv_osmulW, LinearEquiv.symm_apply_apply]
    exact hx
  obtain ⟨s', hs'⟩ := exists_isLift A Sall (gmap γ.1 N) (gmap γ'.1 N') hLa hgN hgN' hD hcD hx'
  have hs : A.IsLift Sall N N' c x ((TI.conjH γ.1 γ'.1).symm s') := TI.isLift_conj A Sall γ.1 γ'.1 N N' c x s' hs'
  have hemb : embH (X.embC A.σ₀) A.δ s' = (TI.RV A γ γ') (embH (X.embC A.σ₀) A.δ ((TI.conjH γ.1 γ'.1).symm s')) := by
    rw [TI.RV_embH]
    congr 1
    exact ((TI.conjH γ.1 γ'.1).apply_symm_apply s').symm
  rw [thInd_eq_lift' A Sall (gmap γ.1 N) (gmap γ'.1 N') hLa hgN hgN' c hc _ s' hs' _,
    thInd_eq_lift' A Sall N N' hLa hN hN' c hc x _ hs _, hpull]

  have hL : LamC (X.embC A.σ₀) A.δ A.AA (gmap γ.1 N) (gmap γ'.1 N') = imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N') :=
    (TI.imgLat_laV A γ γ' _ _ fun y => TI.mem_perO_gmap A.AA γ.1 γ'.1 N N' y).symm
  have hAc : AC (X.embC A.σ₀) A.δ A.AA Sall (gmap γ.1 N) (gmap γ'.1 N') c = imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c) :=
    (TI.imgLat_laV A γ γ' _ _ fun y => TI.mem_halfAO_equiv (TI.conjH γ.1 γ'.1) (TI.mem_perO_gmap A.AA γ.1 γ'.1 N N') Sall c y).symm
  have hBc : BC (X.embC A.σ₀) A.δ A.AA Sall (gmap γ.1 N) (gmap γ'.1 N') c = imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) :=
    (TI.imgLat_laV A γ γ' _ _ fun y => TI.mem_halfBO_equiv (TI.conjH γ.1 γ'.1) (TI.mem_perO_gmap A.AA γ.1 γ'.1 N N') Sall c y).symm
  have hI : imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) ((LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) = imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c) := by
    ext y
    rw [AddSubgroup.mem_inf, KS.MM.mem_imgLat, KS.MM.mem_imgLat, KS.MM.mem_imgLat, AddSubgroup.mem_inf]
  rw [hL, hAc, hBc]

  obtain ⟨hθ, hlev⟩ := (heisHyp_of A a b Sall hLa).2.2.2.2 N N' hN hN'
  obtain ⟨hSc, hr1, hr2, -⟩ := hlev c hc
  have hIso : IsIsom (HV A.sc) (HV A.sc) ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) := TI.isIsom_RV A hst γ γ'
  have hα : ∀ v, alV A.d A.sc ((TI.RV A γ γ') v) = alV A.d A.sc v := TI.alV_RV A hst γ γ'

  have hcard : (repsOf (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c))).card =
      (repsOf (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) ((LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c))).card := by
    have hr1' : relIdx (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) ≠ 0 := by
      rw [← hI, KS.MM.relIdx_map]; exact hr1
    rw [Formalism.L2.Th1.H.Tri.card_reps (repsOf_spec _ _ hr1'), Formalism.L2.Th1.H.Tri.card_reps (repsOf_spec _ _ hr1), ← hI]
    exact KS.MM.relIdx_map _ _ _

  have he : ∀ v, A.e a b (gmap γ.1 N) (gmap γ'.1 N') ((TI.RV A γ γ') v) = A.e a b N N' v := fun v => by
    rw [hEq γ γ' N N' hN hN' ((TI.RV A γ γ') v), hpull]
  have hsum : ∀ v, sumU (HV A.sc) (alV A.d A.sc) (repsOf (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N')) (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c))) (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) ((TI.RV A γ γ') v) =
      sumU (HV A.sc) (alV A.d A.sc) (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) (A.e a b N N') v := by
    intro v
    have hr2' : relIdx (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N')) (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) ≠ 0 := by
      rw [KS.MM.relIdx_map]; exact hr2
    have hSB' := KS.MM.semiChar_map (HV A.sc) (HV A.sc) (TI.RV A γ γ') hIso (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) (alV A.d A.sc) (alV A.d A.sc) hα hSc.2.2.1
    have hfix' := KS.MM.fixedBy_map (HV A.sc) (HV A.sc) (TI.RV A γ γ') hIso (LamC (X.embC A.σ₀) A.δ A.AA N N') (alV A.d A.sc) (alV A.d A.sc) hα
      (A.e a b N N') (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) he hθ
    rw [sumU_eq_inter hSc.1 hSB' hfix' (repsOf_spec _ _ hr2') hr2' ((TI.RV A γ γ') v), sumU_eq_inter hSc.1 hSc.2.2.1 hθ (repsOf_spec _ _ hr2) hr2 v,
      KS.MM.inter_map (HV A.sc) (HV A.sc) hSc.1 hSc.1 (TI.RV A γ γ') hIso (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) (alV A.d A.sc) (alV A.d A.sc) hα hSc.2.2.1 hr2
        (A.e a b N N') (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) he hθ v, KS.MM.relIdx_map]
  rw [hcard, hemb, hα, ← map_neg (TI.RV A γ γ'),
    KS.MM.opU_map (HV A.sc) (HV A.sc) (TI.RV A γ γ') hIso _ _ hsum]

end Formalism.L2.Ker
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.Cd.CarC

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m} (u : Pr.Word)
  {D : Car} (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem thIndEq_ambOf_car (hok : s.Ok) (hcc : Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Cd.TaylorLogMetric.IsChi D χ)
    {a b : ℕ} (ha : Even a) (hb : Even b) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) {D' : ℕ} (hD : 0 < D')
    (hLa : (Cd.ambOf s B χ cD : Amb X).LaHyp a b Sall) : (Cd.ambOf s B χ cD : Amb X).ThIndEq a b Sall D' :=
  theta_coset_indicator_natural X _ a b Sall D' (ambOf_conj s B χ cD hok) hD hLa
    (eqLaw_ambOf_of s B χ cD hok (Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SqG.eqP_car B hcc hδ χ hχ) ha hb)

theorem thEquivP_ambOf_tiesD (hok : s.Ok) (hcc : Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Cd.TaylorLogMetric.IsChi D χ)
    (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) (hT : LawTies W Ch sel mu cst G) (hTu : 0 < Pr.T u) {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ)
    (he : ∀ τ, (e τ : ℚ) = (W.row τ).e ⟨i, hi⟩)
    (hLa : (Cd.ambOf s B χ cD : Amb X).LaHyp (R.N i) (R.N (i + 1)) (Sall sel mu u))
    (hrat : (Cd.ambOf s B χ cD : Amb X).JetsRatDeg (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i)) :
    ThEquivP (stepT W Ch sel mu cst (Cd.ambOf s B χ cD) u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho := by
  have he' : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩ := by
    intro τ
    rw [he τ, ← hT.2.2.2 u τ]
    rfl
  exact thEquivP_stepT_ofD W Ch sel mu cst (Cd.ambOf s B χ cD) u hi e he' hrat (eOmega_ambOf_of s B χ cD (B.stdOK hcc hδ) _ _)
    (thIndEq_ambOf_car s B χ cD hok hcc hδ hχ (even_rankN R i) (even_rankN R (i + 1)) _ (modulus_pos sel mu cst u hTu) hLa)
    (chiLaw_ambOf_of s B χ cD hok hχ (even_rankN R i) (even_rankN R (i + 1)))
    (muProdLaw_of hX hPr hsel hg hT i hi e he _) (muProdLaw_of hX hPr hsel hg hT i hi e he _)

end Step

section All

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {u : Pr.Word} {m2 : ℕ}
  {D : Car} (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

end All

end Formalism.L2.Ker.Cd.CarC
