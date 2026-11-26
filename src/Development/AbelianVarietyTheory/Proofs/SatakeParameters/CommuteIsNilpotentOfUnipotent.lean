module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLePageHeight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst.DpstMap

section Letter

variable {LL U D D' : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] [AddCommGroup D'] [Module LL D']
  (m : U →+* End LL D) (m' : U →+* End LL D') (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)

def letterLin (T : D →ₗ[LL] D') (hT : ∀ c, T ∘ₗ m c = m' c ∘ₗ T) : Letter m F τ →ₗ[F] Letter m' F τ :=
  Submodule.mapQ _ _ (T.baseChange F) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_iSup_of_mem c ⟨T.baseChange F y, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hT c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this])

end Letter

section Dmap

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V')

def tensV : V ⊗[ℚ_[l]] Bst P →ₗ[LL] V' ⊗[ℚ_[l]] Bst P := AlgebraTensorModule.map f LinearMap.id

theorem tensV_onB (T : End ℚ_[l] (Bst P)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f (onB P LL V T x) = onB P LL V' T (tensV P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tensV_stRep (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f (stRep P ρ g x) = stRep P ρ' g (tensV P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [tensV, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable {ρ ρ' f}

theorem tensV_mem_Dpst (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    tensV P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hK⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← tensV_stRep P ρ ρ' f hf, hK g hg]⟩

def dmap (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) : ↥(Dpst P ρ) →ₗ[LL] ↥(Dpst P ρ') :=
  (tensV P f).restrict (tensV_mem_Dpst P hf)

variable (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
include hf

theorem dmap_phiD (x : ↥(Dpst P ρ)) : dmap P hf (phiD P ρ x) = phiD P ρ' (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_monD (x : ↥(Dpst P ρ)) : dmap P hf (monD P ρ x) = monD P ρ' (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_actD (g : ↥(GK K)) (x : ↥(Dpst P ρ)) : dmap P hf (actD P ρ g x) = actD P ρ' g (dmap P hf x) :=
  Subtype.ext (tensV_stRep P ρ ρ' f hf g x.1)

theorem dmap_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) : dmap P hf (mulD P ρ c x) = mulD P ρ' c (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (n : ℤ) (x : ↥(Dpst P ρ)) :
    dmap P hf (((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) x) =
      ((phiU P ρ' ^ n : (End LL ↥(Dpst P ρ'))ˣ) : End LL ↥(Dpst P ρ')) (dmap P hf x) := by
  have hinv : ∀ y, dmap P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y) =
      (((phiU P ρ')⁻¹ : (End LL ↥(Dpst P ρ'))ˣ) : End LL ↥(Dpst P ρ')) (dmap P hf y) := by
    intro y
    have h1 : phiD P ρ' (dmap P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y)) =
        dmap P hf y := by
      rw [← dmap_phiD, ← coe_phiU, ← End.mul_apply, Units.mul_inv]; rfl
    rw [← h1, ← coe_phiU, ← End.mul_apply, Units.inv_mul]; rfl
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, coe_phiU,
      coe_phiU, dmap_phiD]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, hinv]

end Dmap

section Lin

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
  {ρ : Representation ↥LL.1 ↥(GK K) V} {ρ' : Representation ↥LL.1 ↥(GK K) V'} {f : V →ₗ[↥LL.1] V'}
  (hf : ∀ g v, f (ρ g v) = ρ' g (f v))

def wdLin : WDSpace P ι ρ →ₗ[ℂ] WDSpace P ι ρ' :=
  letI := algC ι LL
  letterLin (mulD P ρ) (mulD P ρ') ℂ (urC ι) (dmap P hf) fun c => LinearMap.ext fun x => dmap_mulD P hf c x

@[simp] theorem wdLin_mk (x : ↥(Dpst P ρ)) : wdLin P ι hf (wdMk P ι ρ x) = wdMk P ι ρ' (dmap P hf x) := rfl

theorem wdLin_wdN (y : WDSpace P ι ρ) : wdLin P ι hf (wdN P ι ρ y) = wdN P ι ρ' (wdLin P ι hf y) := by
  have : (wdLin P ι hf).comp (wdN P ι ρ) = (wdN P ι ρ').comp (wdLin P ι hf) :=
    LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
      simp only [LinearMap.comp_apply, wdN_mk, wdLin_mk, dmap_monD]
  exact LinearMap.congr_fun this y

end Lin

section Weil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
  {ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V} {ρ' : Representation ↥LL.1 ↥(GK Bw.Kw) V'} {f : V →ₗ[↥LL.1] V'}
  (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]

theorem dmap_weilD (σ : ↥(Weil h)) (x : ↥(Dpst P ρ)) :
    dmap P hf (weilD Bw h P ρ σ x) = weilD Bw h P ρ' σ (dmap P hf x) := by
  rw [weilD_apply, weilD_apply]
  exact (dmap_actD P hf _ _).trans (congrArg _ (dmap_phiU_zpow P hf _ x))

theorem wdLin_wdRho (σ : ↥(Weil h)) (y : WDSpace P ι ρ) :
    wdLin P ι hf (wdRho P ι Bw h hj ρ σ y) = wdRho P ι Bw h hj ρ' σ (wdLin P ι hf y) := by
  have : (wdLin P ι hf).comp (wdRho P ι Bw h hj ρ σ) = (wdRho P ι Bw h hj ρ' σ).comp (wdLin P ι hf) :=
    LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
      simp only [LinearMap.comp_apply, wdRho_mk, wdLin_mk, dmap_weilD]
  exact LinearMap.congr_fun this y

end Weil

section Charpoly

theorem charpoly_dvd_of_surjective {K M M' : Type} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup M'] [Module K M'] [FiniteDimensional K M'] (F : M →ₗ[K] M') (hF : Function.Surjective F)
    (T : Module.End K M) (T' : Module.End K M') (hT : ∀ x, F (T x) = T' (F x)) :
    T'.charpoly ∣ T.charpoly := by
  have hA : ∀ x ∈ LinearMap.ker F, T x ∈ LinearMap.ker F := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [hT, hx, map_zero]
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (LinearMap.ker F) T hA]
  refine Dvd.intro_left (T.restrict hA).charpoly ?_
  let e := F.quotKerEquivOfSurjective hF
  have he : (LinearMap.ker F).mapQ (LinearMap.ker F) T (fun x hx => hA x hx) = e.symm.conj T' := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.symm_symm]
    apply e.injective
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    simp only [e, LinearMap.quotKerEquivOfSurjective_apply_mk, hT]
    rfl
  rw [he, LinearEquiv.charpoly_conj]

theorem isNilpotent_zpow_sub_one {R : Type} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1)) (n : ℤ) :
    IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
  have hnat : ∀ k : ℕ, IsNilpotent ((u : R) ^ k - 1) := fun k => by
    rw [← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    exact Commute.sum_left _ _ _ fun i _ =>
      ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    exact hnat k
  · rw [zpow_negSucc]
    have e : (((u ^ (k + 1))⁻¹ : Rˣ) : R) - 1 = (((u ^ (k + 1))⁻¹ : Rˣ) : R) * -(((u : R) ^ (k + 1)) - 1) := by
      rw [mul_neg, mul_sub, mul_one, ← Units.val_pow_eq_pow_val, Units.inv_mul]; abel
    rw [e]
    refine Commute.isNilpotent_mul_left ?_ (hnat (k + 1)).neg
    refine Commute.neg_right ?_
    rw [← Units.val_pow_eq_pow_val]
    exact (Commute.units_inv_left (Commute.refl _)).sub_right (Commute.one_right _)

theorem commute_isNilpotent_of_unipotent {R : Type} [Ring R] {a b : R} (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (n : ℤ) (hc : Commute (u : R) b) (hb : b = a * ((u ^ n : Rˣ) : R)) : Commute a b ∧ IsNilpotent (b - a) := by
  have hUb : Commute ((u ^ n : Rˣ) : R) b := hc.units_zpow_left n
  have ha : a = b * (((u ^ n)⁻¹ : Rˣ) : R) := by rw [hb, mul_assoc, Units.mul_inv, mul_one]
  have haU : Commute a ((u ^ n : Rˣ) : R) := by
    rw [ha]
    exact hUb.symm.mul_left (Commute.units_inv_left (Commute.refl _))
  refine ⟨?_, ?_⟩
  · rw [hb]; exact (Commute.refl a).mul_right haU
  · have e : b - a = a * (((u ^ n : Rˣ) : R) - 1) := by rw [hb, mul_sub, mul_one]
    rw [e]
    exact Commute.isNilpotent_mul_left (haU.sub_right (Commute.one_right _)) (isNilpotent_zpow_sub_one u hu n)

end Charpoly

section Semisimple

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

theorem charpoly_wdRep (σ : ↥(Weil h)) :
    ((wdRep P ι Bw h hj ρ).ρ σ).charpoly = (wdRho P ι Bw h hj ρ σ).charpoly := by
  obtain ⟨u, -, hu, -, hcomm, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  obtain ⟨h1, h2⟩ := commute_isNilpotent_of_unipotent u hu (deg σ) (hcomm σ) (hρ σ)
  exact GlobalTheory.WeilDeligne.charpoly_eq_of_isNilpotent_sub h1 h2

theorem charPol_wdPst [FiniteDimensional ↥LL.1 V] (hV : IsPst P ρ) (σ : ↥(Weil h)) :
    WD.charPol (wdPst P ι Bw h hj ρ) σ = (wdRho P ι Bw h hj ρ σ).charpoly := by
  rw [wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk, charpoly_wdRep]

end Semisimple

end GlobalTheory.Pst.DpstMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiCrysOfConstituent
noncomputable section

namespace GlobalTheory.WordJumpsCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTW

section Clauses

variable (D : D7)

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Clauses

section Constituent

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_toLL : Continuous (D.nbr i w hw).toLL :=
  continuous_subtype_val.comp (D.nbr i w hw).eO_cont

theorem continuous_toGlobal :
    Continuous fun g : Br.G D.nbr i w hw => decS D.nd w (Br.iota D.nbr i w hw g) :=
  continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)

theorem loc_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) : Br.loc D.nbr i w hw M g a b =
      (D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) := rfl

theorem continuous_loc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous (Br.loc D.nbr i w hw M) := by
  refine continuous_matrix fun a b => ?_
  simp only [loc_apply]
  exact (continuous_toLL D i w hw).comp
    ((hM.comp (continuous_toGlobal D i w hw)).matrix_elem a b)

theorem toLLK_toK (c : D.nd.O i) :
    Br.toLLK (D.nbr i w hw) (toK D.nd i c) = (D.nbr i w hw).toLL c :=
  Br.toLLK_alg (D.nbr i w hw) c

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Constituent

section At

variable (D : D7) (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end At

end GlobalTheory.WordJumpsCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.MainNotions.G

abbrev MP (R : Type) [CommRing R] (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) R

def genM (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MP R n) := Matrix.of fun a s => X (a, s)

def cofAct (R : Type) [CommRing R] (n : ℕ) : MP R n →ₐ[R] MP R n :=
  aeval fun v => (genM R n).adjugate v.2.rev v.1

def nuDual {m : ℕ} (ν : Fin (m + 1) → ℕ) : Fin (m + 1) → ℕ := fun i => ν 0 - ν i.rev

def CofRel (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (f g : MP R (m + 1)) : Prop :=
  (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * g = cofAct R (m + 1) f

def stdN (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (dualWeyl O n n ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def stdD (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (weyl O n n le_rfl ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def rnd (Kf : Type) [Field Kf] {n : ℕ} (e : ℤ) (g : Matrix (Fin n) (Fin n) Kf) : MP Kf n →ₗ[Kf] MP Kf n :=
  g.det ^ (-e) • (rowAct Kf g⁻¹).toLinearMap

def twLat {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n : ℕ} (e : ℤ) (S : Submodule O (MP Kf n))
    (g : Matrix (Fin n) (Fin n) Kf) : Submodule O (MP Kf n) :=
  S.map ((rnd Kf e g).restrictScalars O)

def PosOk (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν ν' : Fin n → ℕ) (e e' c : ℤ)
    (tw : Matrix (Fin n) (Fin n) Kf → Matrix (Fin n) (Fin n) Kf) (Ψ : MP Kf n →ₗ[Kf] MP Kf n) : Prop :=
  (∀ f ∈ dualWeyl Kf n n ν, Ψ f = 0 → f = 0) ∧
  (dualWeyl Kf n n ν).map Ψ = dualWeyl Kf n n ν' ∧
  (∀ h : Matrix (Fin n) (Fin n) Kf, IsUnit h.det → ∀ f ∈ dualWeyl Kf n n ν,
    Ψ (rnd Kf e h f) = h.det ^ c • rnd Kf e' (tw h) (Ψ f)) ∧
  (stdN O Kf n ν).map (Ψ.restrictScalars O) = stdN O Kf n ν' ∧
  (stdD O Kf n ν).map (Ψ.restrictScalars O) = stdD O Kf n ν'

end GlobalTheory.ValCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SecondTwistSmallIffExactlyAtAndFinClause
noncomputable section

namespace GlobalTheory.Cmp.SmallJumps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW Module
open GlobalTheory.IndefiniteRowSideFullHecke

theorem finite_of_jumps {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) (anti : ∀ a, F (a + 1) ≤ F a) (exh : ∀ x ∈ U, ∃ a, x ∈ F a)
    (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = (J.count a : ℤ)) :
    FiniteDimensional L U := by
  have hA : Antitone F := antitone_int_of_succ_le anti
  have hd : Antitone fun a => finrank L (F a) := antitone_int_of_succ_le fun a => by
    have := h a
    omega
  obtain ⟨a₀, ha₀⟩ := Multiset.exists_mem_of_ne_zero hJ
  have hpos : 0 < finrank L (F a₀) := by
    have := h a₀
    have := Multiset.count_pos.2 ha₀
    omega
  have hfin : ∀ a ≤ a₀, FiniteDimensional L (F a) := fun a ha =>
    Module.finite_of_finrank_pos (lt_of_lt_of_le hpos (hd ha))
  obtain ⟨b, hb⟩ := J.toFinset.bddBelow
  have hb' : ∀ a ∈ J, b ≤ a := fun a ha => hb (by simpa using ha)
  have hb0 : b ≤ a₀ := hb' a₀ ha₀
  have hst : ∀ a ≤ b, F a = F b := by
    intro a ha
    induction a, ha using Int.leInductionDown with
    | base => rfl
    | pred a ha ih =>
      haveI := hfin (a - 1) (by omega)
      have h1 := h (a - 1)
      have h2 : J.count (a - 1) = 0 := Multiset.count_eq_zero.2 fun hm => by
        have := hb' _ hm
        omega
      rw [sub_add_cancel, h2] at h1
      rw [← ih]
      exact (Submodule.eq_of_le_of_finrank_eq (hA (by omega)) (by omega)).symm
  haveI := hfin b hb0
  refine Submodule.finiteDimensional_of_le (S₂ := F b) fun x hx => ?_
  obtain ⟨a, ha⟩ := exh x hx
  rcases le_total a b with hab | hab
  · rwa [← hst a hab]
  · exact hA hab ha

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_anti : Antitone fun a => FilV PD (LL := LL) (V := V) a := by
  refine antitone_int_of_succ_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem filV_exh (x : TensorProduct Qp V BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, v ⊗ₜ ⟨b, ha⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_anti PD (min_le_left a b) ha)
      (filV_anti PD (min_le_right a b) hb)⟩

theorem finite_ddRE_of_multV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, multV PD ρ τ a = (J.count a : ℤ)) : FiniteDimensional LL (DdRE PD ρ τ) :=
  finite_of_jumps (FildR PD ρ τ) _
    (fun a => inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1)))
    (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩) J hJ h

end Periods

theorem linearIndepOn_of_invariant {K F W G ι : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (v : ι → W) (hv : ∀ g i, σ g (v i) = v i)
    (s : Finset ι) (h : LinearIndepOn K v s) : LinearIndepOn F v s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hx' : x ∉ (s : Set ι) := hx
    rw [Finset.coe_insert, linearIndepOn_insert hx'] at h ⊢
    refine ⟨ih h.1, fun hm => h.2 ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' F).1 hm
    have key : ∀ i ∈ s, ∀ g, a g (c i) = c i := by
      intro i hi g
      have h1 : ∑ i ∈ s, a g (c i) • v i = v x := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hv g x, ← hc, map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hσ, hv]
      have h2 := linearIndepOn_finset_iff.1 (ih h.1) (fun j => a g (c j) - c j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, h1, hc, sub_self]) i hi
      exact sub_eq_zero.1 h2
    rw [← hc]
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨k, hk⟩ := hinv _ (key i hi)
    rw [← hk, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem finite_of_invariant {K F W G : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] [Module.Finite F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (U : Submodule K W)
    (hU : ∀ x ∈ U, ∀ g, σ g x = x) : Module.Finite K U := by
  rw [← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := finrank F W) fun s hs => ?_) (Cardinal.natCast_lt_aleph0)
  have h1 : LinearIndepOn K (fun x : U => (x : W)) s := hs.map' U.subtype U.ker_subtype
  have h2 := linearIndepOn_of_invariant a σ hσ hinv (fun x : U => (x : W))
    (fun g x => hU x x.2 g) s h1
  simpa using LinearIndependent.fintype_card_le_finrank h2

section FieldPeriods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem finite_ddR_of_isField (hF : IsField BdR) [Module.Finite Qp V] (ρ : Representation LL G V) :
    Module.Finite LL (DdR PD ρ) := by
  letI : Field BdR := hF.toField
  haveI := PD.finK
  let σ : G → TensorProduct Qp BdR V →ₗ[Qp] TensorProduct Qp BdR V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  let U : Submodule K (TensorProduct Qp BdR V) :=
    { carrier := {x | ∀ g, σ g x = x}
      zero_mem' := fun g => map_zero _
      add_mem' := fun hx hy g => by rw [map_add (f := _), hx g, hy g]
      smul_mem' := fun c x hx g => by
        rw [← algebraMap_smul BdR c x, hσ, hx g, AlgEquiv.commutes] }
  haveI : Module.Finite K U := finite_of_invariant (F := BdR) (fun g b => PD.actdR g b)
    (fun g => (σ g).toAddMonoidHom) hσ PD.invdR U fun _ hx => hx
  haveI : Module.Finite Qp U := Module.Finite.trans K U
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let f : DdR PD ρ →ₗ[Qp] U :=
    { toFun := fun x => ⟨TensorProduct.comm Qp V BdR x, fun g => by
        have := x.2
        simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero] at this
        rw [hc, this g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V BdR) c _) }
  haveI : Module.Finite Qp (DdR PD ρ) := Module.Finite.of_injective f fun x y h =>
    Subtype.ext ((TensorProduct.comm Qp V BdR).injective (congrArg Subtype.val h))
  exact Module.Finite.of_restrictScalars_finite Qp LL _

end FieldPeriods

variable (D : D7)

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

variable {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))

end Place

variable {D}

end GlobalTheory.Cmp.SmallJumps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeAndBound
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeAndBound
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem wMax_le_and_ge : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wMax D : ℝ) ≤ 8 / 5 * L.sc.b' ∧ ∀ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g → ⌊(hcAt D g).e j⌋ ≤ (wMax D : ℤ) := by
  intro D L C hR
  have hb : (0 : ℝ) ≤ L.sc.b' := by
    obtain ⟨-, h1, -, h3, -⟩ := hR
    linarith
  have hmem : ∀ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat},
      (s : ℝ) ≤ 8 / 5 * L.sc.b' := by
    rintro s ⟨g, j, hg, rfl⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.T.floor_size_bounds_not_thick_embedding L C g j hR hg
    have h100 : (100 : ℝ) ≤ L.sc.w'' D.R.n := hR.2.1
    have hpos : (0 : ℤ) ≤ ⌊(hcAt D g).e j⌋ := by
      have : (0 : ℝ) ≤ (⌊(hcAt D g).e j⌋ : ℝ) := by linarith
      exact_mod_cast this
    have : ((⌊(hcAt D g).e j⌋.toNat : ℤ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ) := by
      rw [Int.toNat_of_nonneg hpos]
    have h' : ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ) := by
      rw [← this]; norm_cast
    rw [h']; exact h2
  have hbdd : BddAbove {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} := by
    refine ⟨⌊8 / 5 * L.sc.b'⌋₊, fun s hs => ?_⟩
    exact Nat.le_floor (hmem s hs)
  refine ⟨?_, ?_⟩
  · unfold wMax
    rcases Set.eq_empty_or_nonempty {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} with he | hne
    · rw [he, csSup_empty]; simp; linarith
    · obtain ⟨s, hs, hseq⟩ : ∃ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}, s = sSup {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} :=
        ⟨_, Nat.sSup_mem hne hbdd, rfl⟩
      rw [← hseq]; exact hmem s hs
  · intro g j hg
    have h1 : ⌊(hcAt D g).e j⌋.toNat ≤ wMax D := le_csSup hbdd ⟨g, j, hg, rfl⟩
    calc ⌊(hcAt D g).e j⌋ ≤ (⌊(hcAt D g).e j⌋.toNat : ℤ) := Int.self_le_toNat _
      _ ≤ (wMax D : ℤ) := by exact_mod_cast h1

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeAndBoundStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wMax D : ℝ) ≤ 8 / 5 * L.sc.b' ∧ ∀ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g → ⌊(hcAt D g).e j⌋ ≤ (wMax D : ℤ) := by
  first | exact @GlobalTheory.HTW.wMax_le_and_ge | exact GlobalTheory.HTW.wMax_le_and_ge | (intros; apply GlobalTheory.HTW.wMax_le_and_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnimodularLatticeLocalConjSymm
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

noncomputable section

namespace GlobalTheory.GO.UniExt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

private theorem mem_localization_iff_exists_smul_mem {N : Submodule (𝓞 E) (Sp E n)} (Q : HeightOneSpectrum (𝓞 E))
    (x : Sp E n) : x ∈ localization₂ Q.asIdeal N ↔ ∃ s ∉ Q.asIdeal, s • x ∈ N := by
  unfold localization₂ locS
  exact Iff.rfl

private theorem mem_iff_hStd_integral_of_isUnimodular {N : Submodule (𝓞 E) (Sp E n)}
    (hu : IsUnimodular (hStd E n) N) (x : Sp E n) :
    x ∈ N ↔ ∀ y ∈ N, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = hStd E n y x := by
  unfold IsUnimodular dual at hu
  conv_lhs => rw [← hu]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]

private theorem hStd_smul_left (a : 𝓞 E) (y z : Sp E n) :
    hStd E n (a • y) z = algebraMap (𝓞 E) E (cO E a) * hStd E n y z := by
  rw [← algebraMap_smul E a y, LinearMap.map_smulₛₗ₂, smul_eq_mul]
  rfl

private theorem hStd_smul_right (a : 𝓞 E) (y z : Sp E n) :
    hStd E n y (a • z) = algebraMap (𝓞 E) E a * hStd E n y z := by
  rw [← algebraMap_smul E a z, map_smul, smul_eq_mul]

private theorem cO_mem_conjP_iff (P : HeightOneSpectrum (𝓞 E)) (t : 𝓞 E) :
    cO E t ∈ (conjPrime₂ P).asIdeal ↔ t ∈ P.asIdeal := by
  unfold conjPrime₂
  show cO E t ∈ Ideal.comap (cO E) P.asIdeal ↔ _
  rw [Ideal.mem_comap]
  have htt : cO E (cO E t) = t := RingOfIntegers.ext (star_star (t : E))
  rw [htt]

theorem mem_localization_conj_iff {N : Submodule (𝓞 E) (Sp E n)} (hl : N.FG) (hu : IsUnimodular (hStd E n) N)
    (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ localization₂ (conjPrime₂ P).asIdeal N ↔ ∀ y ∈ localization₂ P.asIdeal N, IntAt (conjPrime₂ P) (hStd E n y x) := by
  rw [mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, hsx⟩ y hy
    obtain ⟨t, ht, hty⟩ := (mem_localization_iff_exists_smul_mem P y).1 hy
    obtain ⟨r, hr⟩ := (mem_iff_hStd_integral_of_isUnimodular hu (s • x)).1 hsx (t • y) hty
    unfold IntAt
    refine ⟨r, cO E t * s, ?_, ?_⟩
    · intro hmem
      rcases (conjPrime₂ P).isPrime.mem_or_mem hmem with h | h
      · exact ht ((cO_mem_conjP_iff P t).1 h)
      · exact hs h
    · rw [hr, hStd_smul_left, hStd_smul_right, map_mul]
      ring
  · intro H
    classical
    obtain ⟨S, hS⟩ := hl
    have hloc : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ (conjPrime₂ P).asIdeal ∧
        ∃ r : 𝓞 E, algebraMap (𝓞 E) E s * hStd E n y x = algebraMap (𝓞 E) E r := by
      intro y hy
      have hyN : y ∈ N := hS ▸ Submodule.subset_span hy
      have hyl : y ∈ localization₂ P.asIdeal N :=
        (mem_localization_iff_exists_smul_mem P y).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by rwa [one_smul]⟩
      have hint := H y hyl
      unfold IntAt at hint
      obtain ⟨r, s, hs, h⟩ := hint
      exact ⟨s, hs, r, h⟩
    choose! u hu0 w hw using hloc
    refine ⟨∏ y ∈ S, u y, ?_, ?_⟩
    · intro hmem
      obtain ⟨y, hy, hyu⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (conjPrime₂ P).isPrime)).1 hmem
      exact hu0 y hy hyu
    · rw [mem_iff_hStd_integral_of_isUnimodular hu]
      intro y hy
      rw [← hS] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        refine ⟨(∏ y ∈ S.erase z, u y) * w z, ?_⟩
        rw [hStd_smul_right, ← Finset.mul_prod_erase S u hz, map_mul, map_mul, ← hw z hz]
        ring
      | zero => exact ⟨0, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨ra, hra⟩ := ha
        obtain ⟨rb, hrb⟩ := hb
        exact ⟨ra + rb, by rw [map_add (f := _), hra, hrb, map_add (f := _), LinearMap.add_apply]⟩
      | smul a z _ hz =>
        obtain ⟨rz, hrz⟩ := hz
        exact ⟨cO E a * rz, by rw [hStd_smul_left, map_mul, hrz]⟩

theorem conjP_involutive (Q : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ Q) = Q := by
  unfold conjPrime₂
  apply HeightOneSpectrum.ext
  simp only [Ideal.comap_comap]
  unfold cO
  have hid : (RingOfIntegers.mapRingHom (starRingEnd E)).comp
      (RingOfIntegers.mapRingHom (starRingEnd E)) = RingHom.id (𝓞 E) :=
    RingHom.ext fun x => RingOfIntegers.ext (star_star (x : E))
  rw [hid, Ideal.comap_id]

theorem le_of_forall_localized_eq {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N') : N ≤ N' := by
  intro x hx
  by_contra hnx
  let I : Ideal (𝓞 E) := N'.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x)
  have hI : I ≠ ⊤ := by
    intro htop
    apply hnx
    have h1 : (1 : 𝓞 E) ∈ I := htop ▸ Submodule.mem_top
    simpa [I] using h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hMb : M ≠ ⊥ := by
    rintro rfl
    exact RingOfIntegers.not_isField (K := E) (Ring.isField_iff_maximal_bot.2 hM)
  let Q : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hMb⟩
  have hxQ : x ∈ localization₂ Q.asIdeal N' := by
    rw [← h Q]
    exact (mem_localization_iff_exists_smul_mem Q x).2 ⟨1, (Ideal.ne_top_iff_one _).1 hM.ne_top, by rwa [one_smul]⟩
  obtain ⟨s, hs, hsx⟩ := (mem_localization_iff_exists_smul_mem Q x).1 hxQ
  exact hs (hIM (by simpa [I] using hsx))

theorem unimodular_ext : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N N' : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E N → IsUnimodular (hStd E n) N → Submodule.IsLattice E N' → IsUnimodular (hStd E n) N' → (∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' → localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N') ∧ ((∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' ∨ localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N') → N = N') := by
  intro E _ _ _ n N N' hl hu hl' hu'
  have part1 : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' →
      localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N' := by
    intro Q hQ
    ext x
    rw [mem_localization_conj_iff hl.fg hu Q x, mem_localization_conj_iff hl'.fg hu' Q x, hQ]
  refine ⟨part1, fun hor => ?_⟩
  have hall : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' := by
    intro Q
    rcases hor Q with h | h
    · exact h
    · have h' := part1 (conjPrime₂ Q) h
      rwa [conjP_involutive] at h'
  exact le_antisymm (le_of_forall_localized_eq hall) (le_of_forall_localized_eq fun Q => (hall Q).symm)

end GlobalTheory.GO.UniExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersPageLargeScaleBoundsOfLargeScaleStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roomy_of_large_scale : ∀ eps C A : ℝ, 0 < eps → 100 ≤ C → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → Roomy L C := by
  first | exact @GlobalTheory.HTW.roomy_of_large | exact GlobalTheory.HTW.roomy_of_large | (intros; apply GlobalTheory.HTW.roomy_of_large <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersRoundedSizeBoundWindowStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roundedSizeBound_window : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ (bHat L : ℝ) ∧ (bHat L : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1 := by
  first | exact @GlobalTheory.HTW.bHat_window | exact GlobalTheory.HTW.bHat_window | (intros; apply GlobalTheory.HTW.bHat_window <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGlobalLatticeLocalGiven
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace TupApx

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_pow_smul {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ (a : ℕ) (g0 : Matrix (Fin k) (Fin k) R), algebraMap R K π ^ a • g = g0.map (algebraMap R K) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun ij : Fin k × Fin k => g ij.1 ij.2)
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.coe_ne_zero d) hπ
  choose y hy using hd
  refine ⟨a, Matrix.of fun i j => (u⁻¹ : Rˣ) * y (i, j), ?_⟩
  ext i j
  have h1 : π ^ a = (u⁻¹ : Rˣ) * (d : R) := by rw [hu]; simp
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hy, ← map_pow, h1, map_mul, smul_eq_mul,
    Algebra.smul_def, mul_assoc]



end TupApx

end GlobalTheory.GO
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrExtensionEmbedding
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem exists_finite_ext_numberField_sqrt (Qq E K : Type) [Field Qq] [Field E] [Field K]
    [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : Qq) :
    ∃ (Kf : IntermediateField Qq (AlgebraicClosure Qq)) (s : Kf) (eK : K →+* Kf),
      FiniteDimensional Qq Kf ∧ s ^ 2 = algebraMap Qq Kf a ∧
        ∀ x : E, eK (e x) = algebraMap Qq Kf (i x) := by
  classical
  let Ω := AlgebraicClosure Qq
  letI : Algebra E K := e.toAlgebra
  letI : Algebra E Ω := ((algebraMap Qq Ω).comp i).toAlgebra
  haveI : CharZero E := RingHom.charZero e
  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let f : K →ₐ[E] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap Qq Ω a) (n := 2) two_pos
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := E) (M := K)
  let S : Set Ω := insert s (f '' (T : Set K))
  haveI : Finite S := ((T.finite_toSet.image f).insert s).to_subtype
  let Kf : IntermediateField Qq Ω := IntermediateField.adjoin Qq S
  have hfin : FiniteDimensional Qq Kf :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ x : K, f x ∈ Kf := by
    intro x
    have hx : x ∈ Submodule.span E (T : Set K) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      exact IntermediateField.subset_adjoin Qq S (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul, Algebra.smul_def]
      exact mul_mem (Kf.algebraMap_mem (i c)) hy
  refine ⟨Kf, ⟨s, IntermediateField.subset_adjoin Qq S (Set.mem_insert _ _)⟩,
    (f : K →+* Ω).codRestrict Kf hmem, hfin, Subtype.ext hs, fun x => Subtype.ext ?_⟩
  exact f.commutes x

theorem exists_complete_dvr_ext_numberField_sqrt : ∀ (W Qq E K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [Field E] [Field K] [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : W), ∃ (O Kf : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Field Kf) (_ : Algebra O Kf) (ι : Qq →+* Kf) (j : W →+* O) (w : O) (eK : K →+* Kf), IsFractionRing O Kf ∧ (∀ x : W, ι (algebraMap W Qq x) = algebraMap O Kf (j x)) ∧ j.Finite ∧ IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ w ^ 2 = j a ∧ ∀ x : E, eK (e x) = ι (i x) := by
  intro W Qq E K _ _ _ _ _ _ _ _ _ _ i e a
  obtain ⟨Kf, s, eK, hfin, hs, he⟩ :=
    exists_finite_ext_numberField_sqrt Qq E K i e (algebraMap W Qq a)
  letI : Algebra W Kf := ((algebraMap Qq Kf).comp (algebraMap W Qq)).toAlgebra
  haveI : IsScalarTower W Qq Kf := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI h1 := FormalIsogeny.finite_integralClosure W Qq Kf
  haveI h2 := FormalIsogeny.isDiscreteValuationRing_integralClosure W Qq Kf
  have h3 := FormalIsogeny.isAdicComplete_maximalIdeal_of_finite W (integralClosure W Kf)
  have h4 := integralClosure.isFractionRing_of_finite_extension (A := W) Qq Kf
  have hs' : s ^ 2 = algebraMap W Kf a := hs
  have hint : IsIntegral W s :=
    IsIntegral.of_pow two_pos (hs' ▸ isIntegral_algebraMap)
  exact ⟨integralClosure W Kf, Kf, inferInstance, inferInstance, h2, inferInstance, inferInstance,
    algebraMap Qq Kf, algebraMap W _, ⟨s, hint⟩, eK, h4, fun _ => rfl,
    RingHom.finite_algebraMap.2 h1, h3, Subtype.ext hs', he⟩

end GlobalTheory
end
