module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteChainFrameBottom
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleMapCompInverseFinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleIrreducibleAtRealPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSubspaceEqKerProjDerivationOfSquare
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweSwap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerProjectionMaximalThetaSubspace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSubspaceKernelMaximal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolKernelEqThetaSubspaceOfMatch

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsMatchingFiniteDataBottomLevel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockFImageEqZeroOrExistsEqSmul
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvBotMain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.BotMatch
variable {D : D7}
set_option maxHeartbeats 3200000 in
theorem bottom_matching_of_triangle (hH : GlobalTheory.Published.HoweDualityReal) (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {T : Type} {A A' WW : HSp D}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW) {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E}
    {S : T → Finset (Pl D.host.E)} (hX : X.Is ψ θ α β νH S) (t : T) (hT : GlobalTheory.SquareComm.IsTriple A A' WW (α t) (β t))
    (hν : ChrEq (α t / β t) (νH t))
    (hτ : ∀ v : Pl D.host.F, (∃ w ∈ S t, w.under (𝓞 D.host.F) = v) → ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∀ w ∈ S t, w.under (𝓞 D.host.F) = v → splitPrime τ = w)
    (hram : ∀ w ∈ S t, ¬ GlobalTheory.LFun.UnrAt (α t / β t) w)
    (hunr : ∀ w : Pl D.host.E, (∀ w' ∈ S t, w'.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) →
      GlobalTheory.LFun.UnrAt (α t) w ∧ GlobalTheory.LFun.UnrAt (β t) w)
    (hid : ∀ w ∈ S t, IsSplitIdem D (atPl w 1) ∧ atPl w 1 + cA D (atPl w 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1))
    (hε : X.e t = ∑ w ∈ S t, atPl w 1) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (hf : GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t)) (hf' : GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW (X.f' t)) :
    ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
      (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi)
      (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW (α t) (β t) (X.ω t) (X.ω' t) Pi rf rl p p' ∧
      ((∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW (X.f t) P) = 0) ∨
        ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank) (κ : ℂ),
          p (GlobalTheory.SquareComm.fockF ψ θ true FA FW (X.f t) P) ≠ 0 ∧
          p (GlobalTheory.SquareComm.fockF ψ θ true FA FW (X.f t) P) = κ • p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW (X.f' t) P')) := by
  classical
  have hA := hX.weil t
  have hB := hX.weil' t
  have sA : IsSelfDualC (GlobalTheory.Grid.sgn true A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.rigA.1
  obtain ⟨Bs, Γ, Xc, om, om', h, hTr, hTA, hTB, hLV, hLV', hLW, hP, hPw⟩ :=
    exists_reading_lat hψ FA FA' FW hT hA hB sA hX.rigA'.1 hX.rigW.1 (S t) hτ hram hunr
  obtain rfl := h.ψ
  obtain ⟨R, Rf, hM⟩ := hLM _ _ _ Bs _ _ Γ Xc om om' hTr
  have hg := hTr.geo
  have hinj : Function.Injective fun i : Bs.P => splitPrime (Bs.τ i) := fun i j hij =>
    Subtype.ext ((splitPrime_under (Bs.τ i)).symm.trans ((congrArg (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) hij).trans
      (splitPrime_under (Bs.τ j))))
  have hmem : ∀ i : Bs.P, splitPrime (Bs.τ i) ∈ S t := fun i => (hPw _).2 ⟨i, rfl⟩
  have ha : ∀ i : Bs.P, IsSplitIdem D (atPl (splitPrime (Bs.τ i)) 1) ∧
      atPl (splitPrime (Bs.τ i)) 1 + cA D (atPl (splitPrime (Bs.τ i)) 1) =
        algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV i.1 1) := fun i => by
    have := hid _ (hmem i)
    rwa [splitPrime_under] at this
  have he : X.e t = ∑ i : Bs.P, atPl (splitPrime (Bs.τ i)) 1 := by
    have : S t = Finset.univ.image fun i : Bs.P => splitPrime (Bs.τ i) := by
      ext w; simp [hPw]
    rw [hε, this, Finset.sum_image fun i _ j _ hij => hinj hij]
  choose I I' φ φ' lam hI hI' sφ sφ' nφ nφ' nlam hφφ' eφ eφ' using fun i : Bs.P =>
    local_pair h hM sA hX.rigA.2.1 hLV X.rA'.β X.rW.β hν i (by rw [hP]; exact i.2) (hX.expo t _ (hmem i))
  let Φ : ∀ v : Pl D.host.F, (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if hv : v ∈ Bs.P then φ ⟨v, hv⟩ else Γ.M.vac v
  let Φ' : ∀ v : Pl D.host.F, (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if hv : v ∈ Bs.P then φ' ⟨v, hv⟩ else Γ.M'.vac v
  have e1 : ∀ i : Bs.P, Φ i = φ i := fun i => dif_pos i.2
  have e1' : ∀ i : Bs.P, Φ' i = φ' i := fun i => dif_pos i.2
  have e2 : ∀ v ∉ Bs.P, Φ v = Γ.M.vac v := fun v hv => dif_neg hv
  have e2' : ∀ v ∉ Bs.P, Φ' v = Γ.M'.vac v := fun v hv => dif_neg hv
  have hall : ∀ v, (Φ v ∈ GlobalTheory.WeilM.SB _ ∧ Φ v ≠ 0) ∧ (Φ' v ∈ GlobalTheory.WeilM.SB _ ∧ Φ' v ≠ 0) ∧ Rf.p v (Φ v) = Rf.p' v (Φ' v) := by
    intro v
    by_cases hv : v ∈ Bs.P
    · rw [e1 ⟨v, hv⟩, e1' ⟨v, hv⟩]
      exact ⟨⟨sφ _, nφ _⟩, ⟨sφ' _, nφ' _⟩, hφφ' ⟨v, hv⟩⟩
    · rw [e2 v hv, e2' v hv]
      exact ⟨⟨(hg.hM.vac v).1, (hg.hM.vac v).2.1⟩, ⟨(hg.hM'.vac v).1, (hg.hM'.vac v).2.1⟩, (hM.fin.sph v (by rw [hP]; exact hv)).1⟩
  have ev : ∀ᶠ v in Filter.cofinite, Φ v = Γ.M.vac v := Bs.P.eventually_cofinite_notMem.mono e2
  have ev' : ∀ᶠ v in Filter.cofinite, Φ' v = Γ.M'.vac v := Bs.P.eventually_cofinite_notMem.mono e2'
  obtain ⟨f₀, nf₀, ef₀⟩ := exists_pure_pair true A WW hT.rank.symm Γ.M h.JW h.JX sA hX.rigW.1 hψ hTr.base hg.hV hg.hW hg.hM
    (fun s hs => hLV ▸ GlobalTheory.BigDat.star_mem_conjSub hs) hLW hθ hX.isVac.2.theta (GlobalTheory.BigDat.vac_ne_zero (S := GlobalTheory.Grid.neg A) hX.isVac) hX.isVac.2.lat
    (Subtype.val : Bs.P → _) Subtype.val_injective _ ha he _ _ _ (fun i u => (half_iff (Bs.τ i) (ha i).2 u).1)
    (fun i u => (half_iff (Bs.τ i) (ha i).2 u).2)
    (fun i u => ((Γ.V.bas i)⁻¹).1 * u.map (piW (Bs.τ i)) * ((Γ.W.bas i)⁻¹).1ᵀ)
    (fun i u x => by rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul])
    (fun i u => by
      congr 2
      exact Matrix.ext fun p q => (map_mul (piW (Bs.τ i)) _ _).trans (by rw [piW_atPl_one, one_mul]; rfl))
    (fun i z => by
      obtain ⟨u, hu⟩ := exists_map_piW (Bs.τ i) ((Γ.V.bas i).1 * z * (Γ.W.bas i).1ᵀ)
      refine ⟨u, ?_⟩
      beta_reduce
      rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul,
        Units.inv_mul, transpose_one, Matrix.mul_one])
    I (fun i => GlobalTheory.BigNZ.isLagrModel_of_isLin (hI i)) (hX.fst t)
    (fun x hx => by
      by_contra hn
      exact hx (if_neg fun h' => hn h'.1))
    Φ (fun v => (hall v).1.1) (fun v hv => e2 v fun h' => hv ⟨v, h'⟩ rfl) one_ne_zero
    (fun x hx => by
      rw [one_mul]
      refine Eq.trans ?_ (UpperTheory.stdSectionFirst_eq_prod_local D _ _ (hX.idem t) Bs.P Subtype.val Bs.τ hPw hinj (X.c t) (α t / β t) A WW X.rA.β X.rW.β
        A'.rank hT.rank.symm x hx).symm
      exact Finset.prod_congr rfl fun i _ => by rw [e1 i]; exact eφ i x)
  have dV' : ∀ i : Bs.P, IsUnit ((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i)) := fun i => by
    refine ((Matrix.isUnit_transpose _).2 (Γ.V'.bas i).isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).2 ?_)
    have := RingHom.map_det (Bs.τ i : D.host.E →+* Fv D.host.F i.1) Γ.V'.J
    refine (this ▸ IsUnit.map _ (Ne.isUnit ?_) : IsUnit ((Bs.τ i : D.host.E →+* Fv D.host.F i.1).mapMatrix Γ.V'.J).det)
    rw [h.JW₁, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Formalism.L2.Theta.gram_det_ne A')
  have dW : ∀ i : Bs.P, IsUnit ((Γ.W.J.map (Bs.τ i))ᵀ * (Γ.W.bas i).1) := fun i => by
    refine ((Matrix.isUnit_transpose _).2 ((Matrix.isUnit_iff_isUnit_det _).2 ?_)).mul (Γ.W.bas i).isUnit
    have := RingHom.map_det (Bs.τ i : D.host.E →+* Fv D.host.F i.1) Γ.W.J
    refine (this ▸ IsUnit.map _ (Ne.isUnit ?_) : IsUnit ((Bs.τ i : D.host.E →+* Fv D.host.F i.1).mapMatrix Γ.W.J).det)
    rw [h.JX, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) (Formalism.L2.Theta.gram_det_ne WW)
  obtain ⟨f₁, nf₁, ef₁⟩ := exists_pure_pair false A' WW hT.rank.symm Γ.M' h.JW₁ h.JX hX.rigA'.1 hX.rigW.1 hψ hTr.base hg.hV' hg.hW
    hg.hM' (fun s hs => hLV' ▸ GlobalTheory.BigDat.star_mem_conjSub hs) hLW hθ hX.isVac'.2.theta (GlobalTheory.BigDat.vac_ne_zero hX.isVac')
    hX.isVac'.2.lat (Subtype.val : Bs.P → _) Subtype.val_injective (fun i => cA D (atPl (splitPrime (Bs.τ i)) 1))
    (fun i => ⟨GlobalTheory.BigDat.splitIdem_conj (ha i).1, by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, (ha i).2]⟩)
    (η := cA D (X.e t)) (by rw [he, map_sum]) _ _ _ (fun i u => (half_iff (Bs.τ i) (ha i).2 u).2)
    (fun i u => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact (half_iff (Bs.τ i) (ha i).2 u).1)
    (fun i u => -((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i) * u.map (piW ((Bs.τ i).comp D.sp.cm.sig)) * (Γ.W.J.map (Bs.τ i))ᵀ *
      (Γ.W.bas i).1))
    (fun i u x => by rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, neg_add])
    (fun i u => by
      congr 4
      exact Matrix.ext fun p q => (map_mul (piW ((Bs.τ i).comp D.sp.cm.sig)) _ _).trans (by
        rw [← GlobalTheory.FlipMatch.RowChart.piW_cA_eq, GlobalTheory.DualPairCheck.cA_cA, piW_atPl_one, one_mul]; rfl))
    (fun i z => by
      obtain ⟨g₁, h₁⟩ := dV' i
      obtain ⟨g₂, h₂⟩ := dW i
      obtain ⟨u, hu⟩ := exists_map_piW ((Bs.τ i).comp D.sp.cm.sig) ((g₁⁻¹).1 * (-z) * (g₂⁻¹).1)
      refine ⟨u, ?_⟩
      beta_reduce
      rw [hu, Matrix.mul_assoc _ _ (Γ.W.bas i).1, ← h₁, ← h₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
        Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, neg_neg])
    I' (fun i => GlobalTheory.BigNZ.isLagrModel_of_isLin (hI' i)) (hX.snd t)
    (fun x hx => by
      by_contra hn
      exact hx (if_neg fun h' => hn h'.1))
    Φ' (fun v => (hall v).2.1.1) (fun v hv => e2' v fun h' => hv ⟨v, h'⟩ rfl) (κ := ∏ i, lam i)
    (Finset.prod_ne_zero_iff.2 fun i _ => nlam i)
    (fun x hx => by
      refine Eq.trans ?_ (congrArg (_ * ·) (UpperTheory.stdSectionSecond_eq_prod_local D _ _ (hX.idem t) Bs.P Subtype.val Bs.τ hPw hinj (X.c t) (α t / β t)
        A.rank A' WW X.rA'.β X.rW.β hT.rank.symm x hx).symm)
      beta_reduce
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [e1' i]; exact eφ' i x)
  obtain ⟨L, rL, eL⟩ := UpperTheory.theta_transform_fock_model_eq_of_standard_char D Bs.ψ θ hψ hθ true A WW _ hT.rank.symm Γ.V Γ.W Γ.M h.JW h.JX hg.hM FA FW Bs.emb
    (fun w => by obtain ⟨τ, h1, h2, -, h4⟩ := h.cart w; exact ⟨τ, h1, by rw [h2]; simp, h4⟩) f₀ Φ nf₀
    (fun v => (hall v).1.1) ev (fun v => (hall v).1.2) (ef₀.symm ▸ hf)
  obtain ⟨L', rL', eL'⟩ := UpperTheory.theta_transform_fock_model_eq_of_standard_char D Bs.ψ θ hψ hθ false A' WW _ hT.rank.symm Γ.V' Γ.W Γ.M' h.JW₁ h.JX hg.hM' FA' FW Bs.emb
    (fun w => by obtain ⟨τ, h1, -, h3, h4⟩ := h.cart w; exact ⟨τ, h1, by rw [h3]; simp, h4⟩) f₁ Φ' nf₁
    (fun v => (hall v).2.1.1) ev' (fun v => (hall v).2.1.2) (ef₁.symm ▸ hf')
  rw [ef₀] at eL
  rw [ef₁] at eL'
  have pA : ∀ P, GlobalTheory.TripleAssembly.mapA Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf
      (GlobalTheory.SquareComm.fockF Bs.ψ θ true FA FW (X.f t) P) =
      R.p (L P) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p v (Φ v)) := fun P => by
    have := _root_.GlobalTheory.T.tripleProduct_image_thetaSum_pure hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM 1
      (fun _ => L P) (fun _ => Φ) (fun _ => ⟨fun v => (hall v).1.1, ev⟩) (by
        rw [Fin.sum_univ_one]
        exact Submodule.subset_span ⟨L P, Φ, rL ▸ ⟨P, rfl⟩, fun v => (hall v).1.1, ev, rfl⟩)
    rwa [Fin.sum_univ_one, Fin.sum_univ_one, eL] at this
  have pB : ∀ P, GlobalTheory.TripleAssembly.mapB Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf
      (GlobalTheory.SquareComm.fockF Bs.ψ θ false FA' FW (X.f' t) P) =
      R.p' (L' P) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p' v (Φ' v)) := fun P => by
    have := _root_.GlobalTheory.T.tripleProduct_secondMap_theta_pure hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM 1
      (fun _ => L' P) (fun _ => Φ') (fun _ => ⟨fun v => (hall v).2.1.1, ev'⟩) (by
        rw [Fin.sum_univ_one]
        exact Submodule.subset_span ⟨L' P, Φ', rL' ▸ ⟨P, rfl⟩, fun v => (hall v).2.1.1, ev', rfl⟩)
    rwa [Fin.sum_univ_one, Fin.sum_univ_one, eL'] at this
  have tA := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hψ hθ true A WW FA FW _ _ _ hA
  have tB := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hψ hθ false A' WW FA' FW _ _ _ hB
  obtain ⟨oA, oB⟩ := _root_.GlobalTheory.T.triple_algebra_map_surjective hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨iA, iB⟩ := _root_.GlobalTheory.T.triple_assembly_inverse_finite hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨lA, lB⟩ := _root_.GlobalTheory.T.theta_triple_lift_lie_invariant hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨fA, fB⟩ := _root_.GlobalTheory.T.theta_triple_maps_equivariant hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨dA, dB⟩ := _root_.GlobalTheory.T.theta_triple_lift_lie_equivariant hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  have ir := _root_.GlobalTheory.T.theta_triple_lift_irreducible hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  refine ⟨ModuleCat.of ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf), _, _, GlobalTheory.TripleAssembly.mapA Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf,
    GlobalTheory.TripleAssembly.mapB Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf,
    ⟨hA, hB, ir, ⟨tA.1, tA.2, oA, iA, lA, fA, dA⟩, ⟨tB.1, tB.2, oB, iB, lB, fB, dB⟩⟩, ?_⟩
  refine (em _).imp id fun hn => ?_
  obtain ⟨P, hP0⟩ := not_forall.1 hn
  obtain ⟨g, hg', eg⟩ : R.p (L P) ∈ (Γ.M'.Pol Bs.ψ Bs.emb).map R.p' := hM.real.quot'.onto ▸ Submodule.mem_top
  obtain ⟨P', rfl⟩ : g ∈ LinearMap.range L' := rL' ▸ hg'
  refine ⟨P, P', 1, hP0, ?_⟩
  rw [one_smul]
  refine (pA P).trans (Eq.trans ?_ (pB P').symm)
  rw [eg, funext fun v => (hall v).2.2]
end GlobalTheory.BotMatch
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.fockF_image_eq_zero_or_exists_eq_smul : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ((∀ P, p (fockF W.ψ W.θ true FA FW (X.f t) P) = 0) ∨ ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank) (κ : ℂ), p (fockF W.ψ W.θ true FA FW (X.f t) P) ≠ 0 ∧ p (fockF W.ψ W.θ true FA FW (X.f t) P) = κ • p' (fockF W.ψ W.θ false FA' FW (X.f' t) P')) := by
  intro hH hPr _ hLM
  refine GlobalTheory.BotDict.gBig_three GlobalTheory.BotDict.bottom_dictionary GlobalTheory.BotDict.bottom_dictionary GlobalTheory.BotDict.bottom_dictionary ?_
  intro D T Lc sc G μ₀ C x b hL hd _ _ W i j A A' WW X hX FA FA' FW t hf hf'
  classical
  obtain ⟨_, _, _, _, _, -, -, -, hd⟩ := hd W i j A A' WW X hX
  have e : Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) =
      G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _
  have e' : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _
  refine _root_.GlobalTheory.BotMatch.bottom_matching_of_triangle hH hPr hLM W.ψ_std W.θ_is X hX.is t (hd t).1 (e ▸ chrEq_nu G t i j hL)
    (GlobalTheory.T.exists_embedding_splitPrime_gridLocalTensorPlaces hL t) (fun w hw hu => ?_) (fun w hw => ?_) (GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum hL t).1
    ((GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum hL t).2 _ (hX.is.idem t)).1 FA FA' FW hf hf'
  · have hu' : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E)
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) w := by
      rw [e', ← e]; exact hu
    by_cases hs : w.under (𝓞 D.host.F) ∈ G.pl.S0
    · rcases G.pl.mem_S0_of_sum_eq.1 hs with h | h
      · exact GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace hL t i j w h hu'
      · exact GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ hL t i j w h hu'
    · rcases Finset.mem_union.1 hw with h | h
      · unfold Places.W0 at h
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
        exact hs (by rw [G.pl.under_w hv]; exact hv)
      · exact GlobalTheory.TwistRam.not_unrAt_alpha_div_beta hL t i j w w h rfl hs hu'
  · obtain ⟨ε, hε⟩ := GlobalTheory.StabDense.exists_placeIdem (D := D) (w.under (𝓞 D.host.F))
    have hs : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun hs =>
      hw (G.pl.w _) (Finset.mem_union_left _ (by unfold Places.W0; exact Finset.mem_image_of_mem _ hs)) (G.pl.under_w hs)
    have h1 := GlobalTheory.BasePairChar.unrAt_of_unramAt hε (GlobalTheory.T.level_character_unramified_mu G μ₀ hL t _ ε hε hs (fun P hP => hw P (Finset.mem_union_right _ hP)) j) rfl
    have h2 := GlobalTheory.BasePairChar.unrAt_of_unramAt hε (GlobalTheory.T.grid_characters_unramified G μ₀ hL t _ ε hε hs i).1 rfl
    have h3 := GlobalTheory.BasePairChar.unrAt_of_unramAt hε (GlobalTheory.T.grid_characters_unramified G μ₀ hL t _ ε hε hs i).2 rfl
    have h4 : ∀ n : ℕ, GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (Lc.eta ^ n) w := fun n => by
      induction n with
      | zero => rw [pow_zero]; exact fun _ _ => map_one Circle.toUnits
      | succ n ih => rw [pow_succ]; exact ih.mul h3
    exact ⟨h1.mul (h4 _), h2.mul (h4 _)⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotFinRef
end GlobalTheory.BotFinRef
namespace GlobalTheory.BotFinRef
theorem exists_matching_finiteData_bottomLevel : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  intro hH hP hK hL
  refine gBig_mono (_root_.GlobalTheory.T.fockF_image_eq_zero_or_exists_eq_smul hH hP hK hL) fun {D T Lc sc} G μ₀ C x b hA => ?_
  intro W i j A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨Pi, rf, rl, p, p', hm, hc⟩ := hA W i j A A' WW X hX FA FA' FW t hf hf'
  refine ⟨Pi, rf, rl, p, p', hm, fun Pr Pf q q' r r' e hq hq' hp hp' => ?_⟩
  haveI : Nontrivial Pi := hm.irred.1
  exact exists_smul_of_factor q q' e hq (r (X.f t)) (r' (X.f' t)) (fun P => p (fockF W.ψ W.θ true FA FW (X.f t) P))
    (fun P' => p' (fockF W.ψ W.θ false FA' FW (X.f' t) P')) (hp _ hf) (hp' _ hf') hc
end GlobalTheory.BotFinRef
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bottomLevel_matches_finiteData : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  first | exact @_root_.GlobalTheory.BotFinRef.exists_matching_finiteData_bottomLevel | exact _root_.GlobalTheory.BotFinRef.exists_matching_finiteData_bottomLevel | (intros; apply _root_.GlobalTheory.BotFinRef.exists_matching_finiteData_bottomLevel <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IntertwineOfCompatibleMaps
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
theorem GlobalTheory.BotUniqT.bottomLevel_ker_left : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (p Φ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD 0) := by
  intro hR hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hRf Pi rf rl p p' hm
    Φ hΦ ΦD hΦD hD
  obtain ⟨K₁, g₁, ne₁, max₁, h₁⟩ := _root_.GlobalTheory.T.theta_subspace_kernel_maximal hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨K₂, g₂, ne₂, h₂⟩ := _root_.GlobalTheory.T.thetaSubspace_contains_polKernel hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf
  have hle : K₁ ≤ K₂ := fun x hx =>
    (h₂ x (g₁.1.1 hx)).2 (_root_.UpperTheory.Lit.HoweDuality.twisted_theta_kernel_condition hR hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf K₁ g₁ ne₁ x hx)
  rcases max₁ K₂ g₂ hle with h | h
  · rw [← h₁ Φ hΦ ΦD hΦD hD, ← h, h₂ ΦD hΦD]
  · exact absurd h ne₂
end
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.SquareAgree
theorem _root_.GlobalTheory.BotUniqT.bottomLevel_ker_right : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → (p' Φ₀ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ₀D) := by
  intro hR hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hM Pi rf rl p p' hm
    Φ₀ hΦ₀ Φ₀D hΦ₀D hD
  obtain ⟨K, hK, hKs, hKne⟩ := _root_.GlobalTheory.T.thetaSubspace_eq_ker_projDerivation_of_square hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨KD, hKD, hKDs, hKDne⟩ := _root_.GlobalTheory.T.thetaSubgroup_of_ker_derivation hP Bs Γ Xc om om' R Rf hM
  have h1 : K ≤ KD := fun Φ hΦ => (hKD Φ).2 ⟨hKs.le hΦ, _root_.UpperTheory.Lit.HoweDuality.twisted_theta_jet_condition hR hP Bs Γ Xc om om' R Rf hM K hKs hKne Φ hΦ⟩
  have h2 : KD = K := (_root_.GlobalTheory.T.thetaKernel_projection_isMax hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm K KD hK hKDs h1).resolve_right hKDne
  constructor
  · intro h0
    have hm : Φ₀D ∈ K := (hK Φ₀D).2 ⟨hΦ₀D, Φ₀, hΦ₀, hD, h0⟩
    rw [← h2] at hm
    exact ((hKD _).1 hm).2
  · intro hpm
    have hm : Φ₀D ∈ KD := (hKD _).2 ⟨hΦ₀D, hpm⟩
    rw [h2] at hm
    obtain ⟨_, Φ₁, _, hD₁, h0⟩ := (hK _).1 hm
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact h0
end GlobalTheory.SquareAgree
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotUniqT
private theorem exists_equiv_of_same_kernel {V P₀ P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P₀] [Module ℂ P₀]
    [AddCommGroup P] [Module ℂ P] (S : Submodule ℂ V) (p₀ : V →ₗ[ℂ] P₀) (p : V →ₗ[ℂ] P)
    (h₀ : S.map p₀ = ⊤) (h : S.map p = ⊤) (hk : ∀ x ∈ S, p₀ x = 0 ↔ p x = 0) :
    ∃ E : P₀ ≃ₗ[ℂ] P, ∀ x ∈ S, p x = E (p₀ x) := by
  have s₀ : Function.Surjective (p₀.domRestrict S) := by
    intro y
    have hy : y ∈ S.map p₀ := h₀ ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have s : Function.Surjective (p.domRestrict S) := by
    intro y
    have hy : y ∈ S.map p := h ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : LinearMap.ker (p₀.domRestrict S) = LinearMap.ker (p.domRestrict S) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply]
    exact hk x.1 x.2
  let E : P₀ ≃ₗ[ℂ] P := ((p₀.domRestrict S).quotKerEquivOfSurjective s₀).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans ((p.domRestrict S).quotKerEquivOfSurjective s))
  refine ⟨E, fun x hx => ?_⟩
  have e1 : ((p₀.domRestrict S).quotKerEquivOfSurjective s₀).symm (p₀ x) = Submodule.Quotient.mk ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  show p x = ((p.domRestrict S).quotKerEquivOfSurjective s) ((Submodule.quotEquivOfEq _ _ hker)
    (((p₀.domRestrict S).quotKerEquivOfSurjective s₀).symm (p₀ x)))
  rw [e1]
  rfl
private theorem intertwine_of_compatible_maps {V P₀ P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P₀] [Module ℂ P₀]
    [AddCommGroup P] [Module ℂ P] (S : Submodule ℂ V) (p₀ : V →ₗ[ℂ] P₀) (p : V →ₗ[ℂ] P) (E : P₀ ≃ₗ[ℂ] P)
    (hE : ∀ x ∈ S, p x = E (p₀ x)) (h₀ : S.map p₀ = ⊤) (a : Module.End ℂ P₀) (b : Module.End ℂ P)
    (H : ∀ Φ ∈ S, ∃ Φ' ∈ S, p₀ Φ' = a (p₀ Φ) ∧ p Φ' = b (p Φ)) (x : P₀) : E (a x) = b (E x) := by
  have hx : x ∈ S.map p₀ := h₀ ▸ Submodule.mem_top
  obtain ⟨Φ, hΦ, rfl⟩ := hx
  obtain ⟨Φ', hΦ', h1, h2⟩ := H Φ hΦ
  rw [← h1, ← hE Φ' hΦ', h2, hE Φ hΦ]
private theorem commute_of_two_intertwiners {P₀ P : Type} [AddCommGroup P₀] [Module ℂ P₀] [AddCommGroup P] [Module ℂ P]
    (E E' : P₀ ≃ₗ[ℂ] P) (a : Module.End ℂ P₀) (b : Module.End ℂ P) (hE : ∀ x, E (a x) = b (E x))
    (hE' : ∀ x, E' (a x) = b (E' x)) :
    ((E.trans E'.symm : P₀ ≃ₗ[ℂ] P₀) : Module.End ℂ P₀) * a = a * ((E.trans E'.symm : P₀ ≃ₗ[ℂ] P₀) : Module.End ℂ P₀) := by
  ext x
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [hE, LinearEquiv.symm_apply_eq, hE', LinearEquiv.apply_symm_apply]
theorem bottomLevel_unique_of_triple (hH : GlobalTheory.Published.HoweDualityReal) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m)
    {A A' WW : HSp D} (X : Tri T A A' WW) (hX : IsBottomTri W i j X) (t : T)
    (hT : IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
    (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Pi₀ : ModuleCat.{0} ℂ) (rf₀ : GA D WW → Module.End ℂ Pi₀)
    (rl₀ : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi₀)
    (p₀ : (WO A WW → ℂ) →ₗ[ℂ] Pi₀) (p₀' : (WO A' WW → ℂ) →ₗ[ℂ] Pi₀)
    (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
    (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi)
    (hm₀ : IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi₀ rf₀ rl₀ p₀ p₀')
    (hm : IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p') :
    ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ algF W.ψ W.θ true FA FW, p Φ = c • E (p₀ Φ)) ∧
      ∀ Φ' ∈ algF W.ψ W.θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ := GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D W.ψ W.θ hθ A A' WW FA FA' FW _ _ hT X.m X.fd X.m' X.fd'
    hX.is.meas hX.is.meas' (X.ω t) (X.ω' t) hm.weilA hm.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs A.rank A'.rank Γ Xc om om' hTD
  have kA : ∀ Φ ∈ algF W.ψ W.θ true FA FW, p₀ Φ = 0 ↔ p Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
    rw [_root_.GlobalTheory.BotUniqT.bottomLevel_ker_left hH hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      _root_.GlobalTheory.BotUniqT.bottomLevel_ker_left hH hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  have kB : ∀ Φ ∈ algF W.ψ W.θ false FA' FW, p₀' Φ = 0 ↔ p' Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algB Φ hΦ
    rw [_root_.GlobalTheory.BotUniqT.bottomLevel_ker_right hH hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      _root_.GlobalTheory.BotUniqT.bottomLevel_ker_right hH hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  obtain ⟨EA, hEA⟩ := exists_equiv_of_same_kernel _ p₀ p hm₀.mapA.onto hm.mapA.onto kA
  obtain ⟨EB, hEB⟩ := exists_equiv_of_same_kernel _ p₀' p' hm₀.mapB.onto hm.mapB.onto kB
  have fA : ∀ h ∈ GfC WW, ∀ x, EA (rf₀ h x) = rf h (EA x) := fun h hh =>
    intertwine_of_compatible_maps _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapA.stabX.1 h hh Φ hΦ, hm₀.mapA.eqf h hh Φ hΦ, hm.mapA.eqf h hh Φ hΦ⟩
  have fB : ∀ h ∈ GfC WW, ∀ x, EB (rf₀ h x) = rf h (EB x) := fun h hh =>
    intertwine_of_compatible_maps _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapB.stabX.1 h hh Φ hΦ, hm₀.mapB.eqf h hh Φ hΦ, hm.mapB.eqf h hh Φ hΦ⟩
  have lA : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EA (rl₀ τ Y x) = rl τ Y (EA x) := fun τ Y hY =>
    intertwine_of_compatible_maps _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapA.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩
  have lB : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EB (rl₀ τ Y x) = rl τ Y (EB x) := fun τ Y hY =>
    intertwine_of_compatible_maps _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapB.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩
  let ι := {g // g ∈ GfC WW} ⊕ {x : D.what₂.Tau × Matrix (Fin WW.rank) (Fin WW.rank) ℂ // x.2 ∈ lieAt WW x.1}
  let ρ : ι → Module.End ℂ Pi₀ := Sum.elim (fun g => rf₀ g.1) (fun x => rl₀ x.1.1 x.1.2)
  have hrank : Module.rank ℂ Pi₀ ≤ Cardinal.aleph0 :=
    _root_.GlobalTheory.SquareAgree.rank_polarization_pi_le_aleph0 hH hP D _ _ A A' WW FA FA' FW _ _ _ _ _ _ _ _ e Bs Γ Xc om om'
      cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  have hirr : ∀ N : Submodule ℂ Pi₀, (∀ k, ∀ x ∈ N, ρ k x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    hm₀.irred.2 N (fun g hg x hx => hN (Sum.inl ⟨g, hg⟩) x hx) fun τ Y hY x hx => hN (Sum.inr ⟨(τ, Y), hY⟩) x hx
  have hcomm : ∀ k, ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) * ρ k =
      ρ k * ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) := by
    rintro (⟨g, hg⟩ | ⟨⟨τ, Y⟩, hY⟩)
    · exact commute_of_two_intertwiners EA EB _ _ (fA g hg) (fB g hg)
    · exact commute_of_two_intertwiners EA EB _ _ (lA τ Y hY) (lB τ Y hY)
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar ι Pi₀ ρ hrank hirr _ hcomm
  have hT' : ∀ x, EB.symm (EA x) = c • x := fun x => by
    have := LinearMap.congr_fun hc x
    simpa using this
  haveI : Nontrivial Pi₀ := hm₀.irred.1
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Pi₀)
    have h1 := hT' x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h1
    exact hx h1
  refine ⟨EB, c, hc0, fun Φ hΦ => ?_, fun Φ hΦ => hEB Φ hΦ⟩
  rw [hEA Φ hΦ, ← LinearEquiv.map_smul, ← hT', LinearEquiv.apply_symm_apply]
end GlobalTheory.BotUniqT
end
end
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.theta_bottomLevel_uniqueness : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), ∀ (Pi₀ : ModuleCat.{0} ℂ) rf₀ rl₀ p₀ p₀' (Pi : ModuleCat.{0} ℂ) rf rl p p', IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi₀ rf₀ rl₀ p₀ p₀' → IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' → ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ algF W.ψ W.θ true FA FW, p Φ = c • E (p₀ Φ)) ∧ ∀ Φ' ∈ algF W.ψ W.θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  intro hH hP hK hL
  obtain ⟨CF0, h⟩ := GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ hμ G => ?_⟩
  intro W i j A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  obtain ⟨FA₀, FA₀', FW₀, a, b, s₁, s₂, s₃, hall⟩ := h C hC D large₂ he hx hr T Lc μ hμ G W i j A A' WW X hX
  exact _root_.GlobalTheory.BotUniqT.bottomLevel_unique_of_triple hH hP hL G W i j X hX t (hall t).1 FA FA' FW Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotFinMatch
theorem theta_bottom_finite_match : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' → ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  intro hH hP hK hL
  refine gBig_two (_root_.GlobalTheory.T.theta_bottomLevel_matches_finiteData hH hP hK hL) (_root_.GlobalTheory.T.theta_bottomLevel_uniqueness hH hP hK hL) fun {D T Lc sc} G μ₀ C x b hA hB => ?_
  intro W i j A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, hA'⟩ := hA W i j A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have k1 : ∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p₀ (fockF W.ψ W.θ true FA FW f P) = (e.trans E.symm) (q P ⊗ₜ (c⁻¹ • r) f) := by
    intro f hf P
    have hmem : fockF W.ψ W.θ true FA FW f P ∈ algF W.ψ W.θ true FA FW := Submodule.subset_span ⟨f, P, hf, rfl⟩
    have h1 := hE _ hmem
    rw [hp f hf P] at h1
    rw [LinearEquiv.trans_apply, LinearMap.smul_apply, TensorProduct.tmul_smul, LinearEquiv.map_smul, h1,
      LinearEquiv.map_smul, LinearEquiv.map_smul, LinearEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have k2 : ∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p₀' (fockF W.ψ W.θ false FA' FW f P) = (e.trans E.symm) (q' P ⊗ₜ r' f) := by
    intro f hf P
    have hmem : fockF W.ψ W.θ false FA' FW f P ∈ algF W.ψ W.θ false FA' FW := Submodule.subset_span ⟨f, P, hf, rfl⟩
    have h1 := hE' _ hmem
    rw [hp' f hf P] at h1
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
  obtain ⟨κ, hκ⟩ := hA' Pr Pf q q' (c⁻¹ • r) r' (e.trans E.symm) hq hq' k1 k2
  refine ⟨c * κ, ?_⟩
  rw [LinearMap.smul_apply] at hκ
  rw [mul_smul, ← hκ, smul_smul, mul_inv_cancel₀ hc, one_smul]
end GlobalTheory.BotFinMatch
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bottom_finite_place_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' → ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  first | exact @_root_.GlobalTheory.BotFinMatch.theta_bottom_finite_match | exact _root_.GlobalTheory.BotFinMatch.theta_bottom_finite_match | (intros; apply _root_.GlobalTheory.BotFinMatch.theta_bottom_finite_match <;> assumption)
end
