module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractB

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Alg

variable {k : Type} [Field k] [ValuativeRel k] {F₀ : Type} [Field F₀] {n : ℕ}

private theorem incl_inj :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := fun a b h =>
  Units.ext <| Matrix.ext fun i j => Subtype.ext
    (congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) h)

private theorem infl_incl (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) (y : GL (Fin n) 𝒪[k]) :
    infl rd fb (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) = fb (GeneralLinearGroup.map rd y) := by
  have h : ∃ y' : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' =
      GeneralLinearGroup.map (algebraMap 𝒪[k] k) y := ⟨y, rfl⟩
  unfold infl
  rw [dite_eq_left h, incl_inj h.choose_spec]

private theorem infl_not_mem (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) {x : GL (Fin n) k}
    (hx : x ∉ KO k n) : infl rd fb x = 0 :=
  dif_neg hx

private theorem principal_congruence_le_maximal_compact (rd : 𝒪[k] →+* F₀) : K1 rd n ≤ KO k n := by
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

private theorem infl_left (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) {c : GL (Fin n) k}
    (hc : c ∈ K1 rd n) (x : GL (Fin n) k) : infl rd fb (c * x) = infl rd fb x := by
  by_cases hx : x ∈ KO k n
  · obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨y, rfl⟩ := hx
    rw [← map_mul, infl_incl, infl_incl, map_mul, MonoidHom.mem_ker.1 hu, one_mul]
  · rw [infl_not_mem rd fb hx, infl_not_mem rd fb]
    exact fun h => hx (by simpa using (KO k n).mul_mem ((KO k n).inv_mem (principal_congruence_le_maximal_compact rd hc)) h)

private theorem infl_right (rd : 𝒪[k] →+* F₀) (fb : GL (Fin n) F₀ → ℂ) {c : GL (Fin n) k}
    (hc : c ∈ K1 rd n) (x : GL (Fin n) k) : infl rd fb (x * c) = infl rd fb x := by
  by_cases hx : x ∈ KO k n
  · obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨y, rfl⟩ := hx
    rw [← map_mul, infl_incl, infl_incl, map_mul, MonoidHom.mem_ker.1 hu, mul_one]
  · rw [infl_not_mem rd fb hx, infl_not_mem rd fb]
    exact fun h => hx (by simpa using (KO k n).mul_mem h ((KO k n).inv_mem (principal_congruence_le_maximal_compact rd hc)))

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
private theorem rd_eq_zero (rd : 𝒪[k] →+* F₀) (hrd : Function.Surjective rd) (x : 𝒪[k])
    (hx : valuation k (x : k) < 1) : rd x = 0 := by
  by_contra h0
  obtain ⟨y, hy⟩ := hrd (rd x)⁻¹
  have hxy : rd (1 - x * y) = 0 := by
    rw [map_sub, map_mul, hy, mul_inv_cancel₀ h0, map_one, sub_self]
  have hyle : valuation k (y : k) ≤ 1 := y.2
  have hlt : valuation k ((x * y : 𝒪[k]) : k) < 1 := by
    rw [Subring.coe_mul, map_mul]
    exact mul_lt_one_of_lt_of_le hx hyle
  have hval : valuation k ((1 - x * y : 𝒪[k]) : k) = 1 := by
    have : ((1 - x * y : 𝒪[k]) : k) = 1 - ((x * y : 𝒪[k]) : k) := by push_cast; ring
    rw [this, Valuation.map_one_sub_of_lt _ hlt]
  set u : 𝒪[k] := 1 - x * y with hu
  have hu0 : (u : k) ≠ 0 := fun h => by rw [h, map_zero] at hval; exact zero_ne_one hval
  have hinv : valuation k (u : k)⁻¹ ≤ 1 := by rw [map_inv₀, hval, inv_one]
  have hone : u * ⟨(u : k)⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hu0)
  have := congrArg rd hone
  rw [map_mul, hxy, zero_mul, map_one] at this
  exact zero_ne_one this

end Alg

theorem inflFacts :
    UpperTheory.Gal.InertialTypesAlt.L.InflFacts := by
  intro k _ _ _ _ F₀ _ _ rd hrd n
  have hKO : KO k n = GroundTheory.Automorphic.GLnLocal.integralGL k n := rfl
  have hU : KO k n = PositivityTheory.Rg.Tf.Loc.unitGL k := rfl
  have hopenKO : IsOpen (KO k n : Set (GL (Fin n) k)) := by
    rw [hKO]; exact GroundTheory.Automorphic.GLnLocal.isOpen_integralGL k n
  have hcompKO : IsCompact (KO k n : Set (GL (Fin n) k)) := by
    rw [hKO]; exact GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k n
  obtain ⟨r, hr0, hr1⟩ : ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 := by
    obtain ⟨γ, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := k)
    rcases lt_or_gt_of_ne h1 with h | h
    · exact ⟨γ, zero_lt_iff.2 h0, h⟩
    · exact ⟨γ⁻¹, inv_pos.2 (zero_lt_iff.2 h0), inv_lt_one_of_one_lt₀ h⟩
  obtain ⟨B, hB, hBo, -⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub k n r hr0 hr1
  have hent : ∀ g ∈ B, ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro g hg i j
    have hb : valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r := by
      have : g ∈ (B : Set (GL (Fin n) k)) := hg
      rw [hB] at this
      exact this i j
    have h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    rw [← sub_add_cancel ((g : Matrix (Fin n) (Fin n) k) i j) ((1 : Matrix (Fin n) (Fin n) k) i j)]
    exact Valuation.map_add_le _ (hb.trans hr1.le) h1
  have hBK : B ≤ K1 rd n := by
    intro g hg
    have hgO : g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n :=
      (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff k n).2 ⟨hent g hg, hent _ (B.inv_mem hg)⟩
    obtain ⟨y, rfl⟩ : g ∈ KO k n := hgO
    refine ⟨y, ?_, rfl⟩
    change GeneralLinearGroup.map rd y = 1
    refine Units.ext (Matrix.ext fun i j => ?_)
    have hb : valuation k (((GeneralLinearGroup.map (algebraMap 𝒪[k] k) y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j -
        (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r := by
      have : GeneralLinearGroup.map (algebraMap 𝒪[k] k) y ∈ (B : Set (GL (Fin n) k)) := hg
      rw [hB] at this
      exact this i j
    have h0 := rd_eq_zero rd hrd ((y : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) (by
      refine lt_of_le_of_lt (le_of_eq ?_) (hb.trans_lt hr1)
      congr 1
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> rfl)
    rw [map_sub, sub_eq_zero] at h0
    simp only [GeneralLinearGroup.map_apply, Units.val_one]
    rw [h0]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hopen : IsOpen (K1 rd n : Set (GL (Fin n) k)) := Subgroup.isOpen_mono hBK hBo
  have hclosed : IsClosed (K1 rd n : Set (GL (Fin n) k)) := Subgroup.isClosed_of_isOpen _ hopen
  have hcomp : IsCompact (K1 rd n : Set (GL (Fin n) k)) :=
    hcompKO.of_isClosed_subset hclosed (principal_congruence_le_maximal_compact rd)
  have hclosedKO : IsClosed (KO k n : Set (GL (Fin n) k)) := Subgroup.isClosed_of_isOpen _ hopenKO
  have hsupp : ∀ fb : GL (Fin n) F₀ → ℂ, HasCompactSupport (infl rd fb) := fun fb =>
    HasCompactSupport.intro' hcompKO hclosedKO fun x hx => infl_not_mem rd fb hx
  refine ⟨hU, hopen, hcomp, principal_congruence_le_maximal_compact rd, fun fb y => infl_incl rd fb y, fun fb => ⟨⟨hsupp fb, fun c hc x => ⟨infl_left rd fb hc x, infl_right rd fb hc x⟩⟩, ⟨?_, hsupp fb⟩, ?_⟩⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun z => x⁻¹ * z) ⁻¹' (K1 rd n : Set (GL (Fin n) k)), hopen.preimage (continuous_const.mul continuous_id), by simp [(K1 rd n).one_mem], fun z hz => ?_⟩
    have := infl_right rd fb hz x
    simpa using this
  · intro x hx
    by_contra h
    exact hx (infl_not_mem rd fb h)

end UpperTheory.Gal.InertialTypesAlt.L
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

def itN {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ) (x : A) : A := ∏ i ∈ Finset.range d, τ^[i] x

def IntEl {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (γ : GL (Fin n) k) : Prop :=
  (∀ i, valuation k ((γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i) ≤ 1) ∧ valuation k (γ : Matrix (Fin n) (Fin n) k).det = 1

def FrobeniusTwistedHilbertNinety : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁),
    (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (A : Type) [CommRing A] [Algebra F₁ A] [Finite A] (τ : A ≃+* A), (∀ z, τ (algebraMap F₁ A z) = algebraMap F₁ A (sb z)) →
      (∀ x, τ^[Module.finrank F₀ F₁] x = x) → ∀ c : A, itN τ (Module.finrank F₀ F₁) c = 1 → ∃ y : Aˣ, c * τ y = y

def NormFin : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁),
    (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (A : Type) [CommRing A] [Algebra F₁ A] [Finite A] (τ : A ≃+* A), (∀ z, τ (algebraMap F₁ A z) = algebraMap F₁ A (sb z)) →
      (∀ x, τ^[Module.finrank F₀ F₁] x = x) → ∀ x : A, IsUnit x → τ x = x → ∃ y : A, itN τ (Module.finrank F₀ F₁) y = x

def NormAdic : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (τ : A ≃+* A) (d : ℕ), (∀ x, τ^[d] x = x) → (∀ x ∈ I, τ x ∈ I) →
    ∀ a : A, ∑ i ∈ Finset.range d, τ^[i] a = 1 → ∀ x y : A, IsUnit x → τ x = x → itN τ d y - x ∈ I → ∃ y', itN τ d y' = x

def NormPoly : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ χ : k[X], χ.Monic → (∀ i, valuation k (χ.coeff i) ≤ 1) → valuation k (χ.coeff 0) = 1 →
      ∃ p : K[X], (∀ i, valuation K (p.coeff i) ≤ 1) ∧
        χ.map (algebraMap k K) ∣ ∏ i ∈ Finset.range (Module.finrank k K), p.map ((s ^ i : K ≃ₐ[k] K) : K →+* K) - X

def GoodDelta : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ (n : ℕ) (γ : GL (Fin n) k), IntEl γ → ∃ δ : GL (Fin n) K, GlobalTheory.LBC.norm k s δ = incl K n γ ∧
      (∀ x : GL (Fin n) K, Commute x (incl K n γ) → Commute x δ) ∧
      ∀ g : GL (Fin n) K, g⁻¹ * incl K n γ * g ∈ KO K n → g⁻¹ * δ * g ∈ KO K n

def LatDesc : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ (n : ℕ) (g : GL (Fin n) K), g⁻¹ * galAct s n g ∈ KO K n → ∃ h : GL (Fin n) k, ∃ κ ∈ KO K n, g = incl K n h * κ

def LiftVal : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁),
    (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (n : ℕ) (fb : GL (Fin n) F₀ → ℂ), (∀ a b, fb (b⁻¹ * a * b) = fb a) →
      (∀ δ γ, IsFinNorm sb δ γ → normLift sb fb δ = fb γ) ∧
      ∀ δ x : GL (Fin n) F₁, normLift sb fb (x⁻¹ * δ * galAct sb n x) = normLift sb fb δ

def RedNorm : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ n : ℕ, (∀ h : GL (Fin n) k, incl K n h ∈ KO K n ↔ h ∈ KO k n) ∧ (∀ β ∈ KO K n, GlobalTheory.LBC.norm k s β ∈ KO K n) ∧
      (∀ β g : GL (Fin n) K, GlobalTheory.LBC.norm k s (g⁻¹ * β * galAct s n g) = g⁻¹ * GlobalTheory.LBC.norm k s β * g) ∧
      (∀ (γ : GL (Fin n) k) (g : GL (Fin n) K), g⁻¹ * incl K n γ * g ∈ KO K n → IntEl γ) ∧
      ∀ fb : GL (Fin n) F₀ → ℂ, (∀ a b, fb (b⁻¹ * a * b) = fb a) →
        (∀ β ∈ KO K n, ∀ γ : GL (Fin n) k, GlobalTheory.LBC.norm k s β = incl K n γ → infl rK (normLift sb fb) β = infl rk fb γ) ∧
        ∀ κ ∈ KO K n, ∀ y, infl rK (normLift sb fb) (κ⁻¹ * y * galAct s n κ) = infl rK (normLift sb fb) y

def OrbTransfer : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (θ : G →* G) (K : Subgroup G) (K₀ : Subgroup H),
    (∀ h, j h ∈ K ↔ h ∈ K₀) → ∀ (δ : G) (γ : H), GlobalTheory.BCT.twCent θ δ = (GlobalTheory.BCT.twCent (MonoidHom.id H) γ).map j →
    ∀ (φ : G → ℂ) (f : H → ℂ), (∀ κ ∈ K, ∀ y, φ (κ⁻¹ * y * θ κ) = φ y) →
      (∀ x, φ (x⁻¹ * δ * θ x) ≠ 0 → ∃ h, ∃ κ ∈ K, x = j h * κ) → (∀ h, φ ((j h)⁻¹ * δ * θ (j h)) = f (h⁻¹ * γ * h)) →
      (∀ h, θ (j h) = j h) → GlobalTheory.BCT.twOrb θ K δ φ = GlobalTheory.BCT.twOrb (MonoidHom.id H) K₀ γ f

def Derive : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra k K], Continuous (algebraMap k K) →
    ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
      (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
      ValuativeExtension k K ∧ FiniteDimensional k K ∧ IsGalois k K

end UpperTheory.Gal.InertialTypesAlt.L
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFacts
noncomputable section

open ValuativeRel Matrix GlobalTheory.DZA

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

private theorem mem_int (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  change valuation K (s (x : K)) ≤ 1
  rw [GroundTheory.LocalField.valuation_algEquiv_apply]
  exact x.2

private def resO (s : K ≃ₐ[k] K) : 𝒪[K] →+* 𝒪[K] :=
  (s.toAlgHom.toRingHom.comp (algebraMap 𝒪[K] K)).codRestrict 𝒪[K] fun x => mem_int s x

private theorem resO_coe (s : K ≃ₐ[k] K) (x : 𝒪[K]) : ((resO s x : 𝒪[K]) : K) = s (x : K) := rfl

private theorem resO_inv (s : K ≃ₐ[k] K) (x : 𝒪[K]) : resO s (resO s⁻¹ x) = x := by
  apply Subtype.ext
  rw [resO_coe, resO_coe]
  change s (s.symm (x : K)) = x
  exact s.apply_symm_apply _

private theorem map_res (s : K ≃ₐ[k] K) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s) y) =
      GlobalTheory.LBC.galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) := by
  ext i j
  simp [GlobalTheory.LBC.galAct]
  exact resO_coe s _

private theorem map_res_inv (s : K ≃ₐ[k] K) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map (resO s) (GeneralLinearGroup.map (resO s⁻¹) y) = y := by
  ext i j
  simp [resO_inv]

variable {F₀ F₁ : Type} [Field F₀] [Fintype F₀] [Field F₁] [Algebra F₀ F₁]
    {rk : 𝒪[k] →+* F₀} {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁}

private theorem map_res_red (h : IsRes rk rK s sb) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map rK (GeneralLinearGroup.map (resO s) y) =
      GlobalTheory.LBC.galAct sb n (GeneralLinearGroup.map rK y) := by
  ext i j
  simp [GlobalTheory.LBC.galAct]
  exact h.gal _ _ (resO_coe s _)

private theorem pow_red (h : IsRes rk rK s sb) (j : ℕ) (x : 𝒪[K]) :
    (sb ^ j) (rK x) = rK (resO (s ^ j) x) := by
  induction j generalizing x with
  | zero =>
    have hx : resO (s ^ 0) x = x := Subtype.ext (resO_coe _ x)
    rw [hx]
    rfl
  | succ j ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ← h.gal x (resO s x) (resO_coe s x), ih]
    congr 1

private theorem finrank_dvd [Fintype F₁] (h : IsRes rk rK s sb) :
    Module.finrank k K ∣ orderOf s := by
  have hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [h.frob z, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  have hpow : sb ^ orderOf s = 1 := by
    ext z
    obtain ⟨x, rfl⟩ := h.onto₁ z
    rw [pow_red h, pow_orderOf_eq_one]
    have hx : resO (1 : K ≃ₐ[k] K) x = x := Subtype.ext (resO_coe _ x)
    rw [hx]
    rfl
  have hord : orderOf sb = Module.finrank F₀ F₁ := by
    rw [hsb]
    exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁
  rw [← h.deg, ← hord]
  exact orderOf_dvd_of_pow_eq_one hpow

private theorem mem_zpowers_of_isRes [IsGalois k K] [Fintype F₁] (h : IsRes rk rK s sb)
    (τ : K ≃ₐ[k] K) : τ ∈ Subgroup.zpowers s := by
  have hdvd := finrank_dvd h
  have hcard : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
  have hle : orderOf s ∣ Nat.card (K ≃ₐ[k] K) := orderOf_dvd_natCard s
  have heq : Nat.card (Subgroup.zpowers s) = Nat.card (K ≃ₐ[k] K) := by
    rw [Nat.card_zpowers]
    exact Nat.dvd_antisymm hle (hcard ▸ hdvd)
  rw [Subgroup.eq_top_of_card_eq _ heq]
  exact Subgroup.mem_top τ

end

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.frobFacts :
    UpperTheory.Gal.InertialTypesAlt.L.FrobFacts := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb h
  have key : ∀ (n : ℕ) (z : GL (Fin n) F₁), GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n z) = z := by
    intro n z
    rw [← MonoidHom.comp_apply, ← GlobalTheory.LBC.galAct_mul, inv_mul_cancel, GlobalTheory.LBC.galAct_one]
    rfl
  refine ⟨mem_zpowers_of_isRes h, fun n => ⟨?_, ?_, fun y =>
    ⟨GeneralLinearGroup.map (resO s) y, map_res s n y, map_res_red h n y⟩⟩⟩
  · have hinj : Function.Injective (GlobalTheory.LBC.galAct sb n) := by
      intro a b hab
      calc a = GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n a) := (key n a).symm
        _ = GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n b) := by rw [hab]
        _ = b := key n b
    unfold GlobalTheory.LBC.IsStable K1
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨GeneralLinearGroup.map (resO s) y, ?_, map_res s n y⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
      rw [map_res_red h, hy, map_one]
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y),
        ⟨GeneralLinearGroup.map (resO s⁻¹) y, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
        apply hinj
        rw [← map_res_red h, map_res_inv, hy, map_one]
      · rw [← map_res, map_res_inv]
  · unfold GlobalTheory.LBC.IsStable KO
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨GeneralLinearGroup.map (resO s) y, map_res s n y⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y),
        ⟨_, rfl⟩, by rw [← map_res, map_res_inv]⟩
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SmallRadAlt
noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

def BallLev : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ K : Subgroup (GL (Fin n) k), (K : Set (GL (Fin n) k)) = ball n r → IwLev K ∧ ∀ t, dcos K t = elemSet r {t}

def LevOf : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ D : Subgroup (Fin n → kˣ), IsCompact (D : Set (Fin n → kˣ)) → (∀ d ∈ D, ∀ i, valuation k (d i : k) = 1) →
    ∃ K : Subgroup (GL (Fin n) k), (∀ g, g ∈ K ↔ ∃ a ∈ ball n r, ∃ d ∈ D, g = a * diagT k (Fin n) d) ∧ IwLev K ∧
      ∀ t, dcos K t = elemSet r {x | ∃ d ∈ D, x = t * d}

def SmallRad : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    (∀ U : Set (GL (Fin n) k), U ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ball n r' ⊆ U) ∧
    (∀ W : Set (Fin n → kˣ), W ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ∀ u, Near r' u → u ∈ W) ∧
    (∀ r : ValueGroupWithZero k, r < 1 → ∃ D : Subgroup (Fin n → kˣ), (∀ u, u ∈ D ↔ Near r u) ∧ IsCompact (D : Set (Fin n → kˣ))) ∧
    Continuous (diagT k (Fin n)) ∧ (∃ t : Fin n → kˣ, Strict t) ∧ ∀ t₀ t : Fin n → kˣ, Strict t₀ → Dom t → Strict (t₀ * t)

end UpperTheory.Gal.InertialTypesAlt.L
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormOpen
open ValuativeRel UpperTheory.ConvolutionTheory.Loc

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
theorem UpperTheory.Gal.InertialTypesAlt.L.normOpen :
    UpperTheory.Gal.InertialTypesAlt.L.NormOpen := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ r hr0 hr1
  haveI : Module.Free k E := Module.Free.of_divisionRing k E
  have hc : Continuous (algebraMap k E) := (UpperTheory.V.Z.Tf.Orb.extCont_holds k E).1
  have hS : {z : E | valuation E (z - 1) < r} ∈ nhds (algebraMap k E 1) := by
    rw [map_one]
    exact (IsValuativeTopology.hasBasis_nhds' (1 : E)).mem_of_mem hr0.ne'
  obtain ⟨γ, hγ0, hγ⟩ :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_iff.mp (hc.continuousAt.preimage_mem_nhds hS)
  set d := Module.finrank k E with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hdk : (d : k) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  set δ := valuation k (d : k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ] using hdk
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    clear hδ hδ0 hdk hdpos hd
    induction d with
    | zero => simp
    | succ n ih =>
      push_cast
      exact ((valuation k).map_add _ _).trans (max_le ih (by simp))
  obtain ⟨t, ht0, ht1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  set ε := valuation k t with hεdef
  set μ := min γ δ
  have hμ0 : 0 < μ := lt_min (zero_lt_iff.mpr hγ0) (zero_lt_iff.mpr hδ0)
  have hε0 : 0 < ε := zero_lt_iff.mpr (by simpa [hεdef] using ht0)
  set r₂ := μ * ε
  have hr₂0 : 0 < r₂ := mul_pos hμ0 hε0
  have hr₂μ : r₂ < μ := by
    calc r₂ = μ * ε := rfl
      _ < μ * 1 := mul_lt_mul_of_pos_left ht1 hμ0
      _ = μ := mul_one μ
  have hr₂γ : r₂ < γ := hr₂μ.trans_le (min_le_left _ _)
  have hr₂δ : r₂ < δ := hr₂μ.trans_le (min_le_right _ _)
  have hr₀r₂ : r₂ * δ ≤ r₂ := by
    calc r₂ * δ ≤ r₂ * 1 := mul_le_mul_of_nonneg_left hδ1 zero_le'
      _ = r₂ := mul_one r₂
  refine ⟨r₂ * δ, mul_pos hr₂0 (zero_lt_iff.mpr hδ0), hr₀r₂.trans_lt (hr₂δ.trans_le hδ1), ?_⟩
  intro x hx
  have hmem : ∀ y : k, valuation k (y - 1) ≤ r₂ → valuation E (algebraMap k E y - 1) ≤ r := by
    intro y hy
    exact le_of_lt (hγ (lt_of_le_of_lt hy hr₂γ))
  refine ⟨hmem x (hx.trans hr₀r₂), ?_⟩
  have hg : Matrix.GeneralLinearGroup.scalar (Fin 1) x ∈ UpperTheory.ConvolutionTheory.Loc.ball 1 (r₂ * δ) := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa [Matrix.GeneralLinearGroup.scalar] using hx
  obtain ⟨u, ⟨hu, hud⟩, -⟩ := UpperTheory.ConvolutionTheory.Loc.rootEx k 1 d r₂ hr₂δ _ hg
  have hpow : ∀ (M : Matrix (Fin 1) (Fin 1) k) (m : ℕ), (M ^ m) 0 0 = (M 0 0) ^ m := by
    intro M m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, pow_succ]
  have hw : ((u : Matrix (Fin 1) (Fin 1) k) 0 0) ^ d = (x : k) := by
    have := congrArg (fun g : GL (Fin 1) k => (g : Matrix (Fin 1) (Fin 1) k) 0 0) hud
    simp only [Units.val_pow_eq_pow_val] at this
    rw [← hpow, this]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hw1 : valuation k ((u : Matrix (Fin 1) (Fin 1) k) 0 0 - 1) ≤ r₂ := by
    simpa using hu 0 0
  have hw0 : (u : Matrix (Fin 1) (Fin 1) k) 0 0 ≠ 0 := by
    intro h
    rw [h, zero_pow hdpos.ne'] at hw
    exact x.ne_zero hw.symm
  refine ⟨Units.mk0 (algebraMap k E ((u : Matrix (Fin 1) (Fin 1) k) 0 0))
    ((map_ne_zero (algebraMap k E)).mpr hw0), hmem _ hw1, ?_⟩
  rw [Units.val_mk0, Algebra.norm_algebraMap, ← hd, hw]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.StrictNear
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem sg_diag (σ : E ≃+* E) (u : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) u) = diagT E (Fin n) (sgT σ u) := by
  ext i j
  rw [sg, GeneralLinearGroup.map_apply, val_diagT, val_diagT]
  by_cases h : i = j
  · subst h
    simp [sgT]
  · simp [Matrix.diagonal_apply_ne _ h]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_inj : Function.Injective (diagT E (Fin n)) := by
  intro a b h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h
  simpa [val_diagT] using this

private theorem near_val {r : ValueGroupWithZero E} (hr : r < 1) {s : Fin n → Eˣ} (hs : Near r s) (i : Fin n) :
    valuation E (s i : E) = 1 := by
  have h1 : valuation E ((s i : E) - 1) < valuation E (1 : E) := by
    rw [map_one]
    exact lt_of_le_of_lt (hs i) hr
  have h2 := Valuation.map_add_eq_of_lt_right (valuation E) h1
  simpa using h2

private theorem strict_near {r : ValueGroupWithZero E} (hr : r < 1) {t s : Fin n → Eˣ} (ht : Strict t)
    (hs : Near r s) : Strict (t * s) := by
  have key : ∀ k, valuation E ((t * s) k : E) = valuation E (t k : E) := by
    intro k
    rw [Pi.mul_apply, Units.val_mul, map_mul, near_val hr hs k, mul_one]
  intro i j hij
  rw [key, key]
  exact ht i j hij

private theorem ball_sg {r : ValueGroupWithZero E} {σ : E ≃+* E} (hσ : Isom σ) {a : GL (Fin n) E}
    (ha : a ∈ ball n r) : sg σ a ∈ ball n r := by
  simp only [ball, Set.mem_setOf_eq] at ha ⊢
  intro i j
  have h : ((sg σ a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j
      = σ ((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
    rw [sg, GeneralLinearGroup.map_apply, map_sub]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  rw [h, hσ]
  exact ha i j

private theorem diag_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (hs : Near r s) :
    diagT E (Fin n) s ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases h : i = j
  · subst h
    simpa using hs i
  · simp [Matrix.diagonal_apply_ne _ h, one_apply_ne h]

end

end UpperTheory.Gal.InertialTypesAlt.L

theorem UpperTheory.Gal.InertialTypesAlt.L.suppE :
    UpperTheory.Gal.InertialTypesAlt.L.SuppE := by
  intro E _ _ _ _ n σ q hc r hr0 hr1 A hA
  have hσ : Isom σ := hc.isom
  obtain ⟨K, hK, -, -⟩ := ballSub E n r hr0 hr1
  have bmul : ∀ a ∈ ball n r, ∀ b ∈ ball n r, a * b ∈ ball n r := by
    intro a ha b hb
    rw [← hK] at ha hb ⊢
    exact K.mul_mem ha hb
  have binv : ∀ a ∈ ball n r, a⁻¹ ∈ ball n r := by
    intro a ha
    rw [← hK] at ha ⊢
    exact K.inv_mem ha
  have step : ∀ δ g : GL (Fin n) E, g⁻¹ * δ * sg σ g ∈ UpperTheory.Gal.InertialTypesAlt.L.elemSet r A →
      ∃ k ∈ ball n r, ∃ t ∈ A, ∃ s, UpperTheory.Gal.InertialTypesAlt.L.Near r s ∧
        g⁻¹ * δ * sg σ g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
    intro δ g hg
    obtain ⟨a, ha, b, hb, t, ht, he⟩ := hg
    obtain ⟨k, hk, s, hs, hks⟩ := contractB E n σ hσ t (hA t ht) r hr1 a ha b hb
    exact ⟨k, hk, t, ht, s, hs, he.trans hks⟩
  refine ⟨?_, ?_⟩
  · intro δ g hg
    obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
    refine ⟨g * k⁻¹, t, ht, s, hs, UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs, ?_⟩
    calc (g * k⁻¹)⁻¹ * δ * sg σ (g * k⁻¹)
        = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
          rw [map_mul, map_inv]
          group
      _ = diagT E (Fin n) (t * s) := by
          rw [he]
          group
  · intro δ y d hd hy g
    constructor
    · intro hg
      obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
      have hts : Strict (t * s) := UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs
      have hx : (y⁻¹ * g * k⁻¹)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * g * k⁻¹)
          = diagT E (Fin n) (t * s) := by
        rw [← hy]
        calc (y⁻¹ * g * k⁻¹)⁻¹ * (y⁻¹ * δ * sg σ y) * sg σ (y⁻¹ * g * k⁻¹)
            = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
              rw [map_mul, map_mul, map_inv, map_inv]
              group
          _ = diagT E (Fin n) (t * s) := by
              rw [he]
              group
      obtain ⟨u, hu⟩ := strictNormal E n σ q hc d (t * s) hd hts _ hx
      have h2 : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * s := by
        apply UpperTheory.Gal.InertialTypesAlt.L.diag_inj
        rw [map_mul, map_mul, map_inv, ← UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← hu]
        exact hx
      refine ⟨u, ⟨t, ht, ?_⟩, k, hk, ?_⟩
      · have h3 : d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = s := by
          calc d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = (u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u) / t := by
                simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
            _ = s := by
                rw [h2]
                simp
        rw [h3]
        exact hs
      · rw [← hu]
        group
    · rintro ⟨u, ⟨t, ht, hs⟩, κ, hκ, rfl⟩
      have hid : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) := by
        rw [mul_comm t, div_mul_cancel, div_eq_mul_inv, mul_comm (d * _) u⁻¹, mul_assoc]
      have hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹ := by
        rw [← hy]
        group
      refine ⟨κ⁻¹, binv κ hκ, diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ,
        bmul _ (UpperTheory.Gal.InertialTypesAlt.L.diag_ball hs) _ (UpperTheory.Gal.InertialTypesAlt.L.ball_sg hσ hκ), t, ht, ?_⟩
      rw [hδ]
      calc (y * diagT E (Fin n) u * κ)⁻¹ * (y * diagT E (Fin n) d * (sg σ y)⁻¹)
            * sg σ (y * diagT E (Fin n) u * κ)
          = κ⁻¹ * ((diagT E (Fin n) u)⁻¹ * diagT E (Fin n) d * sg σ (diagT E (Fin n) u)) * sg σ κ := by
            rw [map_mul, map_mul]
            group
        _ = κ⁻¹ * (diagT E (Fin n) t * diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t)) * sg σ κ := by
            rw [UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← map_inv (diagT E (Fin n)) u, ← map_mul, ← map_mul, ← map_mul, hid]
        _ = κ⁻¹ * diagT E (Fin n) t * (diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ) := by
            group
end
end
