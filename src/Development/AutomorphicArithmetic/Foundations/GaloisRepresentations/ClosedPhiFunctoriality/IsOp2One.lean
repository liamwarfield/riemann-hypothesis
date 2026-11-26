module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JointApproxOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInertiaRestrictionCocyclesLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallineBreuilKisinFrame

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

def IsOp2 {l : ℕ} [Fact l.Prime] {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (n₁ n₂ : ℕ) (s : Per.Bcris l)
    (V : Matrix (Fin d) (Fin d) (Per.Bcris l)) : Prop :=
  ∃ U, IsPerU ρ U ∧ V * U.map ⇑(Per.φB l ^ n₂) = s • U.map ⇑(Per.φB l ^ n₁)

def LinkOp2 : Prop :=
  ∀ (R : Type) [CommRing R] (π s : R) (d d' : ℕ) (W Z Zs : Matrix (Fin d) (Fin d) R)
    (W₁ Z₁ Zs₁ : Matrix (Fin d') (Fin d') R) (Pm R₀ : Matrix (Fin d) (Fin d') R),
    Zs * Z = s • (1 : Matrix (Fin d) (Fin d) R) → Z₁ * Zs₁ = s • (1 : Matrix (Fin d') (Fin d') R) →
    (∀ i j, π ∣ (Pm * Z₁ - Z * R₀) i j) → (∀ i j, π ∣ (Pm * W₁ - W * R₀) i j) →
    ∀ i j, π ∣ ((s • (W * Zs)) * Pm - Pm * (s • (W₁ * Zs₁))) i j

def OpOne2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (τ₁ : Per.Acris l), IsUnit (iB l τ₁) → ∀ (K : FinExt l) (N k n₁ n₂ d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l])
    (y y' Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    y * y' = τ₁ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    IsPerU ρ U → iB l τ₁ ^ N • U = (y * Q).map (iB l) →
    (y * Q) * (Q' * y') = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    (Q' * y') * (y * Q) = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    IsUnit (iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N)) ∧
    IsOp2 ρ n₁ n₂ (iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N))
      (((phiA l ^ n₂) (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
        ((y * Q).map ⇑(phiA l ^ n₁) * (Q' * y').map ⇑(phiA l ^ n₂))).map (iB l))

def LinkZ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N M : ℕ), ∃ n : ℕ, ∀ (k d d' : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (F : Frame bk N d ρ) (F' : Frame bk N d' ρ')
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y₁ : Matrix (Fin d') (Fin d') (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T →
    Y₁.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (Q₁ Q₁' : Matrix (Fin d') (Fin d') (Per.Acris l)),
    IsSecQ bk N k F.A Q Q' → IsSecQ bk N k F'.A Q₁ Q₁' → ∀ (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (R : Matrix (Fin d) (Fin d') bk.S),
    (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) →
    ∀ i j, (l : Per.Acris l) ^ M ∣ (Pi.map (zC l) * (Y₁.map (fI l) * Q₁) - (Y.map (fI l) * Q) * R.map (f0 bk)) i j

def OpEx2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n₁ n₂ : ℕ), FixUr K n₁ → FixUr K n₂ →
    ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ m, Frame bk N (tw.d' m) fun g => (tw.ρ' m g).val)
      (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ m, (F m).IsCr) → F₀.IsCr →
      (∀ n', ∃ m, n' ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n' r) →
    ∃ (s : Per.Acris l) (V : Matrix (Fin d) (Fin d) (Per.Acris l)) (V' : ∀ m, Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Per.Acris l)),
      IsUnit (iB l s) ∧ IsOp2 ρ n₁ n₂ (iB l s) (V.map (iB l)) ∧ (∀ m, IsOp2 (tw.ρ' m) n₁ n₂ (iB l s) ((V' m).map (iB l))) ∧
      ∀ M, ∃ m, M ≤ m ∧ ∀ i j, (l : Per.Acris l) ^ M ∣ (V * (tw.Pi m).map (zC l) - (tw.Pi m).map (zC l) * V' m) i j

def FixOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw → ∀ (g : ↥(Weil h)), FixUr Bw.Kw (alpha l g).natAbs

def WeilPhi2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (L : FinExt l) (a : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)]
      (m : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P), m ∈ Dst P R → ∃ x : ↥(Dpst P R),
      (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) = (phiV P ↥L.1 (Fin a → ↥L.1) ^ n₂) m ∧
      ((weilD Bw h P R g x : ↥(Dpst P R)) : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) = (phiV P ↥L.1 (Fin a → ↥L.1) ^ n₁) m

def TieRep2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (L : FinExt l) (a d : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)],
    Module.finrank ℂ (WDSpace P ι R) = a → ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) ↥L.1)
      (e : Fin d → ℤ_[l]), (∀ g j (k : Fin a), R g (fun i => b j i k) = ∑ i, ((ρ g).val i j : ℚ_[l]) • fun i' => b i i' k) →
      ∑ i, (e i : ℚ_[l]) • b i = 1 → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp2 ρ n₁ n₂ s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (((b i).trace : ↥L.1) : Om l))
        (ι.symm (LinearMap.trace ℂ (WDSpace P ι R) (wdRho P ι Bw h hj R g)))

def Tie2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (a d : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), IsCrysAt P Bw r →
    ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]),
      Reads ρ (r.comp Bw.e.symm.toMonoidHom) b e → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp2 ρ n₁ n₂ s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (b i).trace) (wdTr P ι Bw h hj r g)

def ClosedTr : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ)
    (a : ℕ), 1 ≤ a → ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw)
      (J : (E →+* Om l) → Multiset ℤ) (r : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l)), Continuous r → IsSSRep r →
    ∀ (C : Set (Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l))) (g : ↥(Weil h)) (θ : Om l),
      JointApprox r C (fun ρ => wdTr P ι Bw h hj (ρ.comp (Dec (F := E) A).subtype) g) θ →
      (∀ ρ ∈ C, Continuous ρ ∧ GlobalTheory.GalOfCusp.IsSstAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Om l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) →
      wdTr P ι Bw h hj (r.comp (Dec (F := E) A).subtype) g = θ

def PowTr : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x : WD h) (σ : ↥(Weil h)) (n : ℕ),
    GlobalTheory.CongPhi.phiSum x σ n = -(x.charPol (σ ^ n)).nextCoeff

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FrExHolds
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.frEx_holds :
    FrEx := by
  intro l _ K L₀ bk τp hτp P AI T a hL₀ r Cl Cv J hCl hcr
  haveI := K.2
  let N : ℕ := Finset.univ.sup fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup
  have hN : ∀ τ', ∀ n ∈ J τ', |n| ≤ (N : ℤ) := by
    intro τ' n hn
    rw [Int.abs_eq_natAbs]
    have h1 : n.natAbs ≤ ((J τ').map Int.natAbs).sup := Multiset.le_sup (Multiset.mem_map_of_mem _ hn)
    have h2 : ((J τ').map Int.natAbs).sup ≤ N :=
      Finset.le_sup (f := fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup) (Finset.mem_univ τ')
    exact_mod_cast h1.trans h2
  have hsstCl : ∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R :=
    fun ρ₁ h L r' R h1 h2 h3 => (hCl ρ₁ h L r' R h1 h2 h3).1
  have hsst : ∀ m, IsSst P (qRep (Cv.tw.ρ' m)) := fun m =>
    (GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).1 hsstCl
  have hfr : ∀ m, ∃ F : Frame bk N (Cv.tw.d' m) (fun g => (Cv.tw.ρ' m g).val),
      F.IsDR ∧ (IsCrys (P.PD K) (qRep (Cv.tw.ρ' m)) → F.IsCr) := fun m =>
    GlobalTheory.T.exists_breuilKisinFrame_semistable_boundedJumps l K bk τp hτp P AI T N _ (Cv.tw.ρ' m) (Cv.cont' m) (hsst m)
      (GlobalTheory.T.layer_DdR_bounds_alt l K L₀ P AI T a Cl J N hL₀ hN _ (Cv.tw.ρ' m) (Cv.lay m) hCl)
  choose F hFdr hFcr using hfr
  obtain ⟨F₀, -, hF₀cr, rr, hlink⟩ := GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower l K bk τp hτp Cv.d N Cv.ρ Cv.tw F hFdr
  have hFc : ∀ m, (F m).IsCr := fun m =>
    hFcr m ((GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).2 hcr)
  exact ⟨N, F, F₀, rr, hFc, hF₀cr hFc, hlink⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoordEx
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

variable {l : ℕ} [Fact l.Prime]

private def coordPair (P : LocPrime l) (L : FinExt l) (a : ℕ) :
    (Fin a → ↥L.1) →+ Bst P →+ (Fin a → OB P) :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun b i => ((v i : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] b)
      (fun b b' => by funext i; simp [TensorProduct.tmul_add]))
    (fun v v' => by
      ext b i
      simp [TensorProduct.add_tmul])

theorem coordEx_holds : CoordEx := by
  intro l _ P L a
  refine ⟨TensorProduct.liftAddHom (coordPair P L a) ?_, ?_⟩
  · intro r v b
    funext i
    simp only [coordPair, AddMonoidHom.mk'_apply, Pi.smul_apply]
    rw [show ((r • v i : ↥L.1) : Om l) = r • ((v i : ↥L.1) : Om l) from rfl]
    exact TensorProduct.smul_tmul r _ b
  · intro v b i
    rfl

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TestTr
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.testTr_holds :
    TestTr := by
  intro l _ P AI T d s v v₀ t p hv h lam
  subst hv
  let Λ : OB P →ₗ[↥(MaximalUnramifiedExtension l)] Bst P :=
    (TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P)).toLinearMap ∘ₗ lam.rTensor (Bst P)
  have hΛ : ∀ (x : Om l) (b : Bst P), Λ (x ⊗ₜ b) = lam x • b := by
    intro x b
    change TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P) (lam.rTensor (Bst P) (x ⊗ₜ b)) = lam x • b
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  have h1 := congrArg Λ h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, hΛ] at h1
  simp only [hΛ] at h1
  have hc : lam p • (1 : Bst P) = Polynomial.C (lam p • (1 : P.R.B)) := by
    rw [← Polynomial.smul_C, map_one]
  have h2 : (∑ i, lam (t i) • T.eB.symm (v₀ i)) = lam p • (1 : P.R.B) := by
    apply Polynomial.C_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hc, ← h1]
    simp only [Polynomial.smul_C]
  simp only [Algebra.smul_def] at h2
  have h3 := congrArg T.eB h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_one, mul_one, RingEquiv.apply_symm_apply] at h3
  have h4 : ∑ i, uB T (lam (t i)) * v₀ i = uB T (lam p) := h3
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h4, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FixWHolds
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.fixW_holds :
    FixW := by
  intro l _ K bk P AI T n hn s
  set x := f0 bk s with hx
  have hact := ActLaws.act_laws l
  have hσB : ∀ (g : GQ l) (y : Per.Acris l), Per.σB g (iB l y) = iB l (sigA g y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.1
  have hφB : ∀ y : Per.Acris l, Per.φB l (iB l y) = iB l (phiA l y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hfix : ∀ g : ↥(GK K), sigA (g : GQ l) x = x := by
    intro g
    have hxe : x = iA l (WittVector.frobenius (bk.ev (PowerSeries.C (PowerSeries.constantCoeff s)))) := by
      simp only [hx, f0, fA, RingHom.comp_apply, bk.ev_frob]
    rw [hxe, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g]
  have hinj : Function.Injective (iB l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
  set b := T.eB.symm (iB l x) with hb
  have hbfix : ∀ g : ↥(GK K), (P.PD K).actB g b = b := by
    intro g
    apply T.eB.injective
    rw [P.PD_actB, T.actB, hb, RingEquiv.apply_symm_apply, hσB, hfix]
  obtain ⟨c, hc⟩ := (P.PD K).invB b hbfix
  have hc' : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ = b := hc
  have hit : ∀ (m : ℕ) (y : ↥(MaximalUnramifiedExtension l)), (fun z => P.φB z)^[m] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B y) =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((frobUr l ^ m) y) := by
    intro m y
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, phiB_algebraMap, pow_succ', AlgHom.mul_apply]
  have hbn : (fun z => P.φB z)^[n] b = b := by
    rw [← hc', hit, hn ⟨c, c.2.2⟩ c.2.1]
  have htr : ∀ (m : ℕ) (y : P.R.B), T.eB ((fun z => P.φB z)^[m] y) = (Per.φB l)^[m] (T.eB y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.frob, ih]
  have hin : ∀ (m : ℕ) (y : Per.Acris l), (Per.φB l)^[m] (iB l y) = iB l ((phiA l)^[m] y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hφB]
  apply hinj
  have h1 := htr n b
  rw [hbn, hb, RingEquiv.apply_symm_apply, hin] at h1
  rw [RingHom.coe_pow]
  exact h1.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrLimHolds
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLim_holds :
    TrStep → TrLim := by
  intro hstep l _ P AI T K bk Γ _ _ L₀ a r Cl Cv s V V' p θ pv hs hV hV' hlink hθ
  by_contra hne
  have hpθ : p - θ ≠ 0 := sub_ne_zero.mpr hne
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hlnorm : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h := PadicAlgCl.norm_extends l ((l : ℚ_[l]))
    rw [Padic.norm_p] at h
    simpa using h
  have hnp : ∀ (c : ℕ) (x : Om l), ‖(l : Om l) ^ c * x‖ = ((l : ℝ) ^ c)⁻¹ * ‖x‖ := by
    intro c x
    rw [norm_mul, norm_pow, hlnorm, inv_pow]
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt (‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖) hl1
  have hsmall : ∀ x : Om l, ‖x‖ ≤ ‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖ → ‖(l : Om l) ^ c₁ * x‖ ≤ 1 := by
    intro x hx
    rw [hnp, inv_mul_le_iff₀ (pow_pos hl0 c₁), mul_one]
    exact hx.trans hc₁.le
  have hsum0 : 0 ≤ ∑ i, ‖(Cv.b i).trace‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have ht : ∀ i, ‖(l : Om l) ^ c₁ * (Cv.b i).trace‖ ≤ 1 := fun i =>
    hsmall _ (((Finset.single_le_sum (f := fun i => ‖(Cv.b i).trace‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))).trans
      (le_add_of_nonneg_left (norm_nonneg _)))
  have hd : ‖(l : Om l) ^ c₁ * (p - θ)‖ ≤ 1 := hsmall _ (le_add_of_nonneg_right hsum0)
  have hpos : 0 < ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [hnp]
    exact mul_pos (inv_pos.mpr (pow_pos hl0 c₁)) (norm_pos_iff.mpr hpθ)
  obtain ⟨c₂, hc₂⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  have hc₂' : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [← inv_pow]
    exact hc₂.le
  have hdvd : ∀ M : ℕ, (l : Per.Acris l) ^ M ∣ (l : Per.Acris l) ^ c₂ * s := by
    intro M
    obtain ⟨m, hMm, hm⟩ := hlink M
    have hle : ((l : ℝ) ^ m)⁻¹ ≤ ((l : ℝ) ^ M)⁻¹ :=
      inv_anti₀ (pow_pos hl0 M) (pow_le_pow_right₀ hl1.le hMm)
    refine hstep l P AI T s Cv.d (Cv.tw.d' m) (Cv.lay m).m M c₁ c₂ (fun i => (Cv.b i).trace)
      (fun j k => ((Cv.lay m).b j k).trace) (Cv.lay m).c (pv m) p θ (Cv.tw.Pi m) Cv.e (Cv.lay m).e V (V' m)
      hV (hV' m) hm (fun i => (pow_dvd_pow _ hMm).trans (Cv.unit m i)) (fun j => ?_) ((hθ m).trans hle) ht hd hc₂'
    have h := Cv.trace m j
    rw [Matrix.trace_sum] at h
    simp only [Matrix.trace_smul, smul_eq_mul] at h
    exact h.trans hle
  obtain ⟨htor, hcomp, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hz := GlobalTheory.CrZero.eq_zero_of_forall_dvd _ hcomp.toIsHausdorff _ hdvd
  have hs0 : s = 0 := GlobalTheory.CrZero.pow_cancel (l : Per.Acris l) htor c₂ s 0 (by simpa using hz)
  haveI : Nontrivial P.R.B := GlobalTheory.Pst.nontrivial_B P
  haveI : Nontrivial (Per.Bcris l) := T.eB.injective.nontrivial
  rw [hs0, map_zero] at hs
  exact not_isUnit_zero hs
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrIdHolds
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trId_holds :
    TrId := by
  intro l _ B _ u zb hz s d d' m t t' c pv p θ Pi e e' V V' h1 h2 lam
  have hscal : ∀ (z : ℤ_[l]) (x : Om l), u (lam (zOm l z * x)) = zb z * u (lam x) := by
    intro z x
    have hx : zOm l z * x = (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) • x := by
      rw [Algebra.smul_def]
      rfl
    rw [hx, map_smul, smul_eq_mul, map_mul, hz]
  have hk : ∀ k, ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (c k * t' j k)) = s * u (lam (c k * pv k)) := by
    intro k
    simpa using h2 k (lam ∘ₗ LinearMap.mulLeft ↥(MaximalUnramifiedExtension l) (c k))
  have hE : (fun i => zb ((Pi *ᵥ e' - e) i)) = Pi.map zb *ᵥ (fun j => zb (e' j)) - fun i => zb (e i) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have hX : (V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ (fun i => zb ((Pi *ᵥ e' - e) i)) =
      V *ᵥ (fun i => zb (e i)) - Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j)) := by
    rw [hE, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    abel
  have hA := h1 lam
  have hS1 : ∑ i, ((V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ fun i => zb ((Pi *ᵥ e' - e) i)) i * u (lam (t i)) =
      s * u (lam p) - ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
    rw [hX, ← hA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [_root_.Pi.sub_apply]
    ring
  have hS2 : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k)) =
      ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) - ∑ k, s * u (lam (c k * pv k)) := by
    have ha : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ i, zb (Pi i j) * u (lam (t i)) =
        ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
      generalize (V' *ᵥ fun i => zb (e' i)) = w
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hb : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ k, u (lam (c k * t' j k)) = ∑ k, s * u (lam (c k * pv k)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => hk k
    rw [← ha, ← hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, hscal, mul_sub]
  have hS3 : s * u (lam (θ - ∑ k, c k * pv k)) = s * u (lam θ) - ∑ k, s * u (lam (c k * pv k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, mul_sub, Finset.mul_sum]
  rw [hS1, hS2, hS3, map_sub, map_sub, mul_sub]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.PowDvdOfEv
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem link_core {W : Type} [CommRing W] (fr : W →+* W) (c e : W) (hc : fr c = c) {d d' : ℕ}
    (Z Rv : Matrix (Fin d) (Fin d') W) (T A : Matrix (Fin d) (Fin d) W) (T' A' : Matrix (Fin d') (Fin d') W)
    (hZ : Z.map fr = Z) (hT : IsUnit T) (hφ : e • T.map fr = T * A) (hφ' : e • T'.map fr = T' * A')
    (hD : ∀ i j, c ∣ (Z * T' - T * Rv) i j) :
    ∀ i j, c ∣ (Rv * A' - A * Rv.map fr) i j := by
  choose G hG using hD
  have hD' : Z * T' - T * Rv = c • Matrix.of G := by
    ext i j
    simp [hG i j]
  have h1 : Z * T'.map fr - T.map fr * Rv.map fr = c • (Matrix.of G).map fr := by
    have h := congrArg (fun M => M.map fr) hD'
    have e1 : (Z * T' - T * Rv).map fr = Z * T'.map fr - T.map fr * Rv.map fr := by
      rw [Matrix.map_sub _ (map_sub fr), Matrix.map_mul, Matrix.map_mul, hZ]
    have e2 : (c • Matrix.of G).map fr = c • (Matrix.of G).map fr := by
      ext i j
      simp [hc]
    simpa only [e1, e2] using h
  have h2 : T * (Rv * A' - A * Rv.map fr) = c • (e • (Matrix.of G).map fr - Matrix.of G * A') := by
    have e3 : T * Rv = Z * T' - c • Matrix.of G := by rw [← hD']; abel
    calc T * (Rv * A' - A * Rv.map fr)
        = (T * Rv) * A' - (T * A) * Rv.map fr := by
          rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Z * (T' * A') - c • (Matrix.of G * A') - (T * A) * Rv.map fr := by
          rw [e3, Matrix.sub_mul, Matrix.mul_assoc, Matrix.smul_mul]
      _ = e • (Z * T'.map fr - T.map fr * Rv.map fr) - c • (Matrix.of G * A') := by
          rw [← hφ, ← hφ', Matrix.mul_smul, Matrix.smul_mul, smul_sub]
          abel
      _ = c • (e • (Matrix.of G).map fr - Matrix.of G * A') := by
          rw [h1, smul_sub, smul_comm]
  obtain ⟨u, rfl⟩ := hT
  have h3 : Rv * A' - A * Rv.map fr =
      c • ((↑u⁻¹ : Matrix (Fin d) (Fin d) W) * (e • (Matrix.of G).map fr - Matrix.of G * A')) := by
    rw [← Matrix.mul_smul, ← h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  intro i j
  rw [h3, Matrix.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

private theorem pow_dvd_of_ev {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (n : ℕ) (x : bk.S)
    (h : (l : Ainf l) ^ n ∣ bk.ev x) : (l : bk.S) ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := h
    obtain ⟨x', rfl⟩ := bk.dvd_of_dvd_ev x ⟨(l : Ainf l) ^ n * c, by rw [hc, pow_succ', mul_assoc]⟩
    have h0 : bk.ev x' - (l : Ainf l) ^ n * c = 0 := by
      apply ainf_torsionFree
      rw [map_mul, map_natCast, pow_succ', mul_assoc] at hc
      rw [mul_sub, hc, sub_self]
    have h1 : (l : Ainf l) ^ n ∣ bk.ev x' := ⟨c, sub_eq_zero.1 h0⟩
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih x' h1)

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkA_holds :
    LinkA := by
  intro l _ K bk τ hτ N d d' n ρ ρ' F F' Y Y' hY hY' Pi R hlink
  have hev : ∀ s, inclW l (bk.ev s) = bk.evW s := fun s => rfl
  refine ⟨?_, ?_⟩
  · intro i j
    apply GlobalTheory.HTBound.pow_dvd_of_inclW
    have e1 : (Pi.map (Per.zA l)).map (inclW l) = zW Pi := by
      refine Matrix.ext fun a b => ?_
      exact (inclWA l).commutes _
    have e2 : (R.map bk.ev).map (inclW l) = R.map bk.evW := by
      rw [Matrix.map_map]; rfl
    have e : (Pi.map (Per.zA l) * Y' - Y * R.map bk.ev).map (inclW l) =
        inclW l τ ^ N • (zW Pi * F'.T - F.T * R.map bk.evW) := by
      rw [Matrix.map_sub _ (map_sub (inclW l)), Matrix.map_mul, Matrix.map_mul, hY, hY', e1, e2,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left (hlink i j) _
  · have key := link_core (frobW l).toRingHom ((l : WCb l) ^ n) (bk.evW bk.E ^ N) (by simp)
      (zW Pi) (R.map bk.evW) F.T (F.A.map bk.evW) F'.T (F'.A.map bk.evW)
      (by ext i j; simp [zW]) F.unit F.φ F'.φ hlink
    have hfr : (R.map bk.evW).map (frobW l).toRingHom = (R.map (frobS l bk.a)).map bk.evW := by
      refine Matrix.ext fun a b => ?_
      simp only [Matrix.map_apply]
      show frobW l (inclW l (bk.ev (R a b))) = inclW l (bk.ev (frobS l bk.a (R a b)))
      rw [frobW_inclW, bk.ev_frob]
    rw [hfr] at key
    have hmap : R.map bk.evW * F'.A.map bk.evW - F.A.map bk.evW * (R.map (frobS l bk.a)).map bk.evW =
        (R * F'.A - F.A * R.map (frobS l bk.a)).map bk.evW := by
      rw [Matrix.map_sub _ (map_sub bk.evW), Matrix.map_mul, Matrix.map_mul]
    rw [hmap] at key
    intro i j
    apply pow_dvd_of_ev
    apply GlobalTheory.HTBound.pow_dvd_of_inclW
    simpa only [Matrix.map_apply, hev] using key i j
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoordWD
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem letter_lift {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (κ : F →+* B) (f : D →+ M)
    (hL : ∀ (r : LL) (x : D), f (r • x) = κ (algebraMap LL F r) • f x)
    (hU : ∀ (u : U) (x : D), f (m u x) = κ (τ u) • f x) :
    ∃ ψ : Letter m F τ →+ M, (∀ (c : F) (y : Letter m F τ), ψ (c • y) = κ c • ψ y) ∧
      ∀ x : D, ψ (letterMk m F τ x) = f x := by
  letI : Module F M := Module.compHom M κ
  have hsm : ∀ (c : F) (y : M), c • y = κ c • y := fun _ _ => rfl
  let f₂ : F →+ D →+ M := AddMonoidHom.mk' (fun c =>
      (DistribSMul.toAddMonoidHom M (κ c)).comp f)
    (fun c c' => by
      ext x
      simp [add_smul])
  have hf₂ : ∀ c x, f₂ c x = κ c • f x := fun _ _ => rfl
  let g : F ⊗[LL] D →+ M := TensorProduct.liftAddHom f₂ fun r c x => by
    rw [hf₂, hf₂, hL, Algebra.smul_def, map_mul, mul_comm, mul_smul, smul_comm]
  have hg : ∀ c x, g (c ⊗ₜ x) = κ c • f x := fun _ _ => rfl
  have hgs : ∀ (c : F) (y : F ⊗[LL] D), g (c • y) = κ c • g y := fun c y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]
    | tmul c' x => rw [TensorProduct.smul_tmul', hg, hg, smul_eq_mul, map_mul, mul_smul]
  let gL : F ⊗[LL] D →ₗ[F] M := { toFun := g, map_add' := g.map_add, map_smul' := hgs }
  have hk : letterKer m F τ ≤ LinearMap.ker gL := iSup_le fun u => by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    change g _ = 0
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
    | tmul c x =>
      simp only [LinearMap.sub_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply, LinearMap.id_apply,
        map_sub, hgs, hg, hU]
      rw [smul_comm, sub_self]
  let ψL : Letter m F τ →ₗ[F] M := (letterKer m F τ).liftQ gL hk
  refine ⟨ψL.toAddMonoidHom, fun c y => ψL.map_smul c y, fun x => ?_⟩
  change g (1 ⊗ₜ x) = f x
  rw [hg, map_one, one_smul]

set_option synthInstance.maxHeartbeats 400000 in
private theorem coord_smul {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l} {a : ℕ}
    {ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)} (h : IsCoord P L ψ₀) (c : ↥L.1)
    (y : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    ψ₀ (c • y) = (((c : Om l) ⊗ₜ 1 : OB P)) • ψ₀ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]
  | tmul v b =>
    funext i
    rw [TensorProduct.smul_tmul', h, Pi.smul_apply, Pi.smul_apply, h, smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl

private theorem coord_mulV {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l} {a : ℕ}
    {ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)} (h : IsCoord P L ψ₀) (c : ↥(MaximalUnramifiedExtension l))
    (y : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    ψ₀ (GlobalTheory.Pst.mulV P ↥L.1 (Fin a → ↥L.1) c y) = (((c : Om l) ⊗ₜ 1 : OB P)) • ψ₀ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), smul_add, hx, hy]
  | tmul v b =>
    funext i
    rw [GlobalTheory.Pst.mulV_tmul, h, Pi.smul_apply, h, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul]
    rfl

private noncomputable def kap {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) : ℂ →+* OB P :=
  (Algebra.TensorProduct.includeLeftRingHom : Om l →+* OB P).comp ι.symm.toRingHom

private theorem kap_apply {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (z : Om l) :
    kap P ι (ι z) = (z ⊗ₜ 1 : OB P) := by
  change ((ι.symm (ι z) ⊗ₜ 1 : OB P)) = _
  rw [RingEquiv.symm_apply_apply]

section
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K L : FinExt l} {a : ℕ}
  (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
  (ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P))


set_option synthInstance.maxHeartbeats 400000 in
private noncomputable def fD : ↥(GlobalTheory.Pst.Dpst P R) →+ (Fin a → OB P) :=
  { toFun := fun x => ψ₀ x.1, map_zero' := ψ₀.map_zero, map_add' := fun x y => ψ₀.map_add x.1 y.1 }

set_option synthInstance.maxHeartbeats 400000 in
private theorem fD_smul (h : IsCoord P L ψ₀) (ι : Om l ≃+* ℂ) (r : ↥L.1) (x : ↥(GlobalTheory.Pst.Dpst P R)) :
    fD R ψ₀ (r • x) = kap P ι (ι (r : Om l)) • fD R ψ₀ x := by
  exact (coord_smul h r x.1).trans
    (congrArg (fun t : OB P => t • ψ₀ x.1) (kap_apply P ι (r : Om l)).symm)

set_option synthInstance.maxHeartbeats 400000 in
private theorem fD_mul (h : IsCoord P L ψ₀) (ι : Om l ≃+* ℂ) (u : ↥(MaximalUnramifiedExtension l)) (x : ↥(GlobalTheory.Pst.Dpst P R)) :
    fD R ψ₀ (GlobalTheory.Pst.mulD P R u x) = kap P ι (ι (u : Om l)) • fD R ψ₀ x := by
  exact (coord_mulV h u x.1).trans
    (congrArg (fun t : OB P => t • ψ₀ x.1) (kap_apply P ι (u : Om l)).symm)

end

set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.coordWD_holds :
    CoordWD := by
  intro l _ P ι K L a R ψ₀ h
  obtain ⟨ψ, h1, h2⟩ := @letter_lift ↥L.1 ↥(MaximalUnramifiedExtension l) ↥(GlobalTheory.Pst.Dpst P R) _ _ _ _ (GlobalTheory.Pst.mulD P R) ℂ _ (GlobalTheory.Pst.algC ι L)
    (GlobalTheory.Pst.urC ι) (OB P) (Fin a → OB P) _ _ _ (kap P ι) (fD R ψ₀)
    (fun r x => fD_smul R ψ₀ h ι r x) (fun u x => fD_mul R ψ₀ h ι u x)
  exact ⟨ψ, h1, h2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.InvQHolds
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix GlobalTheory.CrTop
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem invQ_holds : InvQ := by
  intro l _ K bk τ hτ N k d ρ F hcr Q Q' hsec g
  obtain ⟨hQQ, hQu₀, hQ'u₀, hQφ₀⟩ := hsec
  obtain ⟨Y, Y', hY, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨-, -, hE2⟩ := GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d (fun g => (ρ g).val) F Y Y' hY hYY
  obtain ⟨htf, -, ⟨v, hv⟩, hφι, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set ι := algebraMap (Ainf l) (Per.Acris l) with hι
  have hQu : ∀ i j, ι (bk.ev X) ∣ (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := hQu₀
  have hQ'u : ∀ i j, ι (bk.ev X) ∣ (Q' - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := hQ'u₀
  change (F.ε g).map (fun a => ι (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q
  set σ := sigA (g : GQ l) with hσdef
  set fA : bk.S →+* Per.Acris l := (ι.comp bk.ev).comp (frobS l bk.a) with hfA
  set f0 : bk.S →+* Per.Acris l := fA.comp ((PowerSeries.C).comp PowerSeries.constantCoeff) with hf0
  have hQφ : fA bk.E ^ N • (Q * F.A.map f0) = f0 bk.E ^ N • (F.A.map fA * Q.map (phiA l)) := hQφ₀
  set ε' := (F.ε g).map (fun a => ι (WittVector.frobenius a)) with hε'
  have hfr : ∀ s : bk.S, fA s = ι (WittVector.frobenius (bk.ev s)) := fun s => by
    simp only [hfA, RingHom.comp_apply, bk.ev_frob]
  have hfix : ∀ c : Wq l bk.a, σ (fA (PowerSeries.C c)) = fA (PowerSeries.C c) := fun c => by
    rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g c]
  have hcomm : ∀ x, phiA l (σ x) = σ (phiA l x) := fun x => GlobalTheory.CrisMaps.phiA_sigA (g : GQ l) x
  have he₀ : ∃ w : (Per.Acris l)ˣ, f0 bk.E = (l : Per.Acris l) * w := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; simp
    refine ⟨((Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map fA.toMonoidHom), ?_⟩
    simp [hf0, hc]
  have hBB : F.A.map fA * F.A'.map fA = fA bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAA : F.A.map f0 * F.A'.map f0 = f0 bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have hσA₀ : (F.A.map f0).map σ = F.A.map f0 := by
    ext i j; simp only [Matrix.map_apply, hf0, RingHom.comp_apply]; exact hfix _
  have hσe₀ : σ (f0 bk.E) = f0 bk.E := by simp only [hf0, RingHom.comp_apply]; exact hfix _
  have hσf : ∀ s : bk.S, ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))) = σ (fA s) := fun s => by
    rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← GlobalTheory.RingBasics.φA_apply, ActLaws.φA_σA]
  have h2 : fA bk.E ^ N • (ε' * (F.A.map fA).map σ) = σ (fA bk.E) ^ N • (F.A.map fA * ε'.map (phiA l)) := by
    have e := congrArg (fun M => M.map (ι.comp WittVector.frobenius)) (hE2 g)
    simp only [map_smul_ring, Matrix.map_mul, Matrix.map_map, map_pow, RingHom.comp_apply] at e
    have hm1 : F.A.map (fun s => ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s)))) =
        (F.A.map fA).map σ := by
      ext i j
      exact hσf _
    have hm2 : F.A.map (fun s => ι (WittVector.frobenius (bk.ev s))) = F.A.map fA := by
      ext i j
      exact (hfr _).symm
    have hm3 : (F.ε g).map (fun a => ι (WittVector.frobenius (WittVector.frobenius a))) =
        ε'.map (phiA l) := by
      ext i j
      exact (hφι _).symm
    change ι (WittVector.frobenius (bk.ev bk.E)) ^ N •
      (ε' * F.A.map (fun s => ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))))) =
      ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev bk.E))) ^ N •
      (F.A.map (fun s => ι (WittVector.frobenius (bk.ev s))) *
        (F.ε g).map (fun a => ι (WittVector.frobenius (WittVector.frobenius a)))) at e
    rw [← hfr, hσf, hm1, hm2, hm3] at e
    exact e
  have hL1 := GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect (Per.Acris l) (phiA l) σ d N k (l : Per.Acris l) (fA bk.E) (f0 bk.E) Q Q' (F.A.map fA) (F.A'.map fA)
    (F.A.map f0) (F.A'.map f0) ε' htf ⟨v, hv⟩ he₀ hcomm (map_natCast _ _) (map_natCast _ _) hσe₀ hσA₀ hQQ hBB hAA hQφ h2
  obtain ⟨w₀, hw₀⟩ := he₀
  set D := Q' * ε' * Q.map σ - (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) with hD
  have hDeq : (l : Per.Acris l) ^ (2 * N) • D = F.A.map f0 * D.map (phiA l) * (((w₀⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) ^ (2 * N) • F.A'.map f0) := by
    rw [Matrix.mul_smul, ← hL1, smul_smul, hw₀]
    congr 1
    rw [mul_pow, mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]
  set u := ι (bk.ev X) with hu
  set π := Ideal.Quotient.mk (Ideal.span {u}) with hπ
  have hz : ∀ M : Matrix (Fin d) (Fin d) (Per.Acris l), (∀ i j, u ∣ M i j) ↔ M.map π = 0 := fun M => by
    constructor
    · intro h; ext i j
      simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using h i j
    · intro h i j
      have := congrFun (congrFun h i) j
      simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
  have hQ1 : Q.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
    rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQu
  have hQ'1 : Q'.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
    rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQ'u
  have hdvdφ : bk.ev X ∣ WittVector.frobenius (bk.ev X) := by
    rw [bk.ev_X, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
    exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero
  have hε1 : ε'.map π = 1 := by
    have : ∀ i j, u ∣ (ε' - 1) i j := fun i j => by
      obtain ⟨c, hc⟩ := hcr g i j
      have e1 : (ε' - 1) i j = ι (WittVector.frobenius ((F.ε g - 1) i j)) := by
        simp only [hε', Matrix.sub_apply, Matrix.map_apply, map_sub]
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      rw [e1, hc, map_mul, map_mul]
      exact dvd_mul_of_dvd_left (map_dvd ι hdvdφ) _
    rw [← sub_eq_zero, ← Matrix.map_one π (map_zero _) (map_one _), ← Matrix.map_sub _ (map_sub π)]
    exact (hz _).1 this
  have hQσ : (Q.map σ).map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
    have hdσ : u ∣ σ u := by
      rw [hu, hσdef, hσι]; exact map_dvd ι ((galois_discMap l K bk).1 (g : GQ l))
    have : ∀ i j, u ∣ (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := fun i j => by
      have e1 : (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j =
          σ ((Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) := by
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      obtain ⟨c, hc⟩ := hQu i j
      rw [e1, hc, map_mul]
      exact dvd_mul_of_dvd_left hdσ _
    rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 this
  have hdiv : ∀ i j, ι (bk.ev X) ∣ D i j := by
    refine (hz D).2 ?_
    rw [hD, Matrix.map_sub _ (map_sub π), Matrix.map_mul, Matrix.map_mul, hQ'1, hε1, hQσ]
    simp only [map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), mul_one, smul_mul_smul_comm, map_pow]
    rw [← pow_add, ← two_mul, sub_self]
  have hD0 := GlobalTheory.T.acris_frobenius_matrix_eq_zero_of_dvd l K bk d (2 * N) D (F.A.map f0) _ hdiv hDeq
  have hM : Q' * ε' * Q.map σ = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) :=
    sub_eq_zero.1 hD0
  refine smul_cancel (pow_cancel htf (2 * k)) ?_
  have := congrArg (fun M => Q * M) hM
  simp only [← Matrix.mul_assoc, hQQ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at this
  exact this

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end
