module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapF
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModel

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

section Abstract

variable {A B : Type}

def prodSpan (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)) : Submodule ℂ (A × B → ℂ) :=
  Submodule.span ℂ {F | ∃ a ∈ U₁, ∃ b ∈ U₂, F = fun x => a x.1 * b x.2}

end Abstract

section Lin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s : ℕ}


variable (E) in
abbrev KO (n : ℕ) : Subgroup (GL (Fin n) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n

def typeF (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) : Submodule ℂ (GA E N → ℂ) where
  carrier := {f | (∀ u ∈ K, ∀ g, f (g * finGL E N u) = f g) ∧
    ∀ g, (fun k : Kinf E N => f (g * infGL E N (Unitary.toUnits k))) ∈ W}
  add_mem' := fun {f f'} h h' => ⟨fun u hu g => by simp only [Pi.add_apply, h.1 u hu g, h'.1 u hu g],
    fun g => W.add_mem (h.2 g) (h'.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  smul_mem' := fun c f h => ⟨fun u hu g => by simp only [Pi.smul_apply, h.1 u hu g],
    fun g => W.smul_mem c (h.2 g)⟩

def typed (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) :
    Submodule ℂ (Sm E N) :=
  U ⊓ (typeF K W).comap (Sm E N).subtype

structure FlatFn (e : GA E N → ℂ) : Prop where
  ne : ∀ x, e x ≠ 0
  rinv : ∀ x (k : Kinf E N), ∀ c ∈ KO E N, e (x * cf N k c) = e x
  sm : e ∈ Sm E N

def Carries (e : GA E N → ℂ) (U U' : Submodule ℂ (Sm E N)) : Prop :=
  ∀ φ ∈ U, ∃ φ' ∈ U', ∀ x, φ'.1 x = e x * φ.1 x

def FinStable (U : Submodule ℂ (Sm E N)) : Prop := ∀ (g : GL (Fin N) (Af E)), ∀ φ ∈ U, act (.fin g) φ ∈ U

def indSpan (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) :=
  Submodule.span ℂ {φ | MemInd2 U₁ U₂ φ}

theorem exists_iw (x : GA E (r + s)) : ∃ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) ∧ x = unip u * lev (Ad E) r s m * cf (r + s) k c := by
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) x)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) x)
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add (f := _), show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add (f := _), show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), k, c, hc, ga_ext ?_ ?_⟩
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf]

def leviOf (x : GA E (r + s)) : GA E r × GA E s := (exists_iw x).choose_spec.choose

def nodeFn (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (x : GA E (r + s)) : ℂ := e₁ (leviOf x).1 * e₂ (leviOf x).2

def absFn (N : ℕ) (w : ℂ) (x : GA E N) : ℂ := (chiDet N (GlobalTheory.CuspRep.Model.absC E w) x : ℂˣ)

end Lin

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def typeHF (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) : Submodule ℂ (H E a b → ℂ) where
  carrier := {F | TypeH K₁ K₂ W₁ W₂ F}
  add_mem' := fun {F F'} h h' => ⟨fun u₁ hu₁ u₂ hu₂ x => by
      simp only [Pi.add_apply, h.1 u₁ hu₁ u₂ hu₂ x, h'.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.add_mem _ (h.2 x) (h'.2 x)⟩
  zero_mem' := ⟨fun _ _ _ _ _ => rfl, fun _ => Submodule.zero_mem _⟩
  smul_mem' := fun c F h => ⟨fun u₁ hu₁ u₂ hu₂ x => by simp only [Pi.smul_apply, h.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.smul_mem _ c (h.2 x)⟩

end Pair

end GlobalTheory.CompanionTheory.LimV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.CompanionTheory.CTSmooth
open PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PExpFin

namespace GlobalTheory.CompanionTheory.HullExp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

def trans (r : ℕ) (s : ℝ) : Module.End ℂ (GA E N → ℂ) where
  toFun f g := f (aT E N r s * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trans_pow (r : ℕ) (s : ℝ) (i : ℕ) (f : GA E N → ℂ) :
    (trans r s ^ i) f = fun g => f (aT E N r (s * i) * g) := by
  induction i generalizing f with
  | zero =>
    funext g
    simp [aT_zero]
  | succ i ih =>
    funext g
    rw [pow_succ, Module.End.mul_apply, ih]
    change f (aT E N r s * (aT E N r (s * i) * g)) = _
    rw [← mul_assoc, ← aT_add]
    congr 3
    push_cast
    ring

theorem kl_iff {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} :
    Kl r s p F ↔ aeval (trans (E := E) (N := N) r s) p F = 0 := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, trans_pow]
  constructor
  · intro h
    funext g
    simpa [Finset.sum_apply] using h g
  · intro h g
    simpa [Finset.sum_apply] using congrFun h g

theorem kl_mul_left {r : ℕ} {s : ℝ} {p : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) (q : ℂ[X]) :
    Kl r s (q * p) F := by
  rw [kl_iff] at h ⊢
  rw [map_mul, Module.End.mul_apply, h, map_zero]

theorem lo_fin {φ : Sm E N} (h : LO φ) (k : GL (Fin N) (Af E)) : LO (act (.fin k) φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ ?_⟩
  · change φ.1 (ratGL E N γ * g * finGL E N k) = φ.1 (g * finGL E N k)
    rw [mul_assoc, h.1]
  · have hc : Continuous fun u : GL (Fin N) (Af E) => k⁻¹ * u * k := by fun_prop
    have hm : {u | finRep E N u φ = φ} ∈ nhds (k⁻¹ * 1 * k) := by
      have : k⁻¹ * 1 * k = 1 := by group
      rw [this]
      exact h.2.mem_nhds (by simp)
    refine Filter.mem_of_superset (hc.continuousAt.preimage_mem_nhds hm) fun u hu => ?_
    have hu' : finRep E N (k⁻¹ * u * k) φ = φ := hu
    change finRep E N u (finRep E N k φ) = finRep E N k φ
    conv_rhs => rw [← hu']
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group

theorem lo_cpt {φ : Sm E N} (h : LO φ) (k : Kinf E N) : LO (act (.cpt k) φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun u hu => ?_)⟩
  · change φ.1 (ratGL E N γ * g * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits k))
    rw [mul_assoc, h.1]
  · have hu' : finRep E N u φ = φ := hu
    apply Subtype.ext
    funext g
    change φ.1 (g * finGL E N u * infGL E N (Unitary.toUnits k)) = φ.1 (g * infGL E N (Unitary.toUnits k))
    have e : φ.1 (g * infGL E N (Unitary.toUnits k) * finGL E N u) = φ.1 (g * infGL E N (Unitary.toUnits k)) :=
      congrArg (fun ψ : Sm E N => ψ.1 (g * infGL E N (Unitary.toUnits k))) hu'
    rw [← e, mul_assoc, mul_assoc, infGL_comm]

theorem lo_act {φ : Sm E N} (h : LO φ) (o : Op E N) : LO (act o φ) := by
  cases o with
  | fin k => exact lo_fin h k
  | cpt k => exact lo_cpt h k
  | lie X => exact lo_lie h X

theorem lo_add {φ ψ : Sm E N} (h : LO φ) (h' : LO ψ) : LO (φ + ψ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
    ((h.2.inter h'.2).mem_nhds ⟨by simp, by simp⟩) fun k hk => ?_)⟩
  · change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [h.1, h'.1]
  · have h1 : finRep E N k φ = φ := hk.1
    have h2 : finRep E N k ψ = ψ := hk.2
    change finRep E N k (φ + ψ) = φ + ψ
    rw [map_add (f := _), h1, h2]

theorem lo_smul {φ : Sm E N} (h : LO φ) (c : ℂ) : LO (c • φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun k hk => ?_)⟩
  · change c * φ.1 _ = c * φ.1 _
    rw [h.1]
  · have h1 : finRep E N k φ = φ := hk
    change finRep E N k (c • φ) = c • φ
    rw [map_smul, h1]

theorem lo_zero : LO (0 : Sm E N) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  have : {k | finRep E N k (0 : Sm E N) = 0} = Set.univ := Set.eq_univ_of_forall fun k => map_zero _
  rw [this]
  exact isOpen_univ

section CT

variable {r : ℕ} [MeasurableSpace (BlockIx N r → Ad E)] [BorelSpace (BlockIx N r → Ad E)]
  (μ : Measure (BlockIx N r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx N r → Ad E))

theorem ct_add_lo (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {φ ψ : Sm E N} (hφ : LO φ) (hψ : LO ψ) :
    PositivityTheory.Affgl.CT.ct μ 𝓕 (φ + ψ).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 + PositivityTheory.Affgl.CT.ct μ 𝓕 ψ.1 := by
  funext g
  exact integral_add (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hφ.1 hφ.2 g)
    (GlobalTheory.CompanionTheory.CTFin.Central.integrable_unip_mul μ 𝓕 h𝓕 hψ.1 hψ.2 g)

theorem kl_act_lo (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) {s : ℝ} {p : ℂ[X]} {φ : Sm E N}
    (hφ : LO φ) (h : Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1)) (o : Op E N) :
    Kl r s p (PositivityTheory.Affgl.CT.ct μ 𝓕 (act o φ).1) := by
  cases o with
  | fin k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.fin k) φ).1 = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * finGL E N k) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | cpt k =>
    have e : PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.cpt k) φ).1 =
        fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (g * infGL E N (Unitary.toUnits k)) := by
      funext g
      exact congrArg (fun f : (BlockIx N r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ)
        (funext fun x => congrArg φ.1 (mul_assoc _ _ _))
    rw [e]
    exact kl_right h _
  | lie X =>
    obtain ⟨F, hF1, hF2⟩ := ct_smooth E N r φ hφ.1 hφ.2 μ 𝓕 inferInstance h𝓕
    have e1 : F.1 = PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 := funext hF1
    have e2 : (lie E N X F).1 = PositivityTheory.Affgl.CT.ct μ 𝓕 (act (.lie X) φ).1 := funext (hF2 X)
    rw [← e2]
    exact kl_lie (e1 ▸ h) X

end CT

def bdSub (r : ℕ) (ρ : ℝ) : Submodule ℂ (Sm E N) where
  carrier := {φ | LO φ ∧ ∃ p : ℂ[X], p.Monic ∧ (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp ρ) ∧ ∀ F, IsCT r φ.1 F → Kl r 1 p F}
  add_mem' := by
    rintro φ ψ ⟨hφ, p, hp, hpz, hpk⟩ ⟨hψ, q, hq, hqz, hqk⟩
    refine ⟨lo_add hφ hψ, p * q, hp.mul hq, fun z hz => ?_, ?_⟩
    · exact (Polynomial.root_mul.1 hz).elim (hpz z) (hqz z)
    · rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
      let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
      have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
      have _ := hμ
      rw [ct_add_lo μ 𝓕 h𝓕 hφ hψ]
      refine (klSub r 1 (p * q)).add_mem ?_ ?_
      · rw [mul_comm]
        exact kl_mul_left (hpk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩) q
      · exact kl_mul_left (hqk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩) p
  zero_mem' := by
    refine ⟨lo_zero, 1, monic_one, fun z hz => ?_, ?_⟩
    · simp [Polynomial.IsRoot] at hz
    · rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
      let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
      have : PositivityTheory.Affgl.CT.ct μ 𝓕 (0 : Sm E N).1 = 0 := by
        funext g
        simp [PositivityTheory.Affgl.CT.ct]
      rw [this]
      exact (klSub r 1 1).zero_mem
  smul_mem' := by
    rintro c φ ⟨hφ, p, hp, hpz, hpk⟩
    refine ⟨lo_smul hφ c, p, hp, hpz, ?_⟩
    rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
    let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
    rw [ct_smul]
    exact (klSub r 1 p).smul_mem c (hpk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩)

theorem isStable_bdSub (r : ℕ) (ρ : ℝ) : _root_.GlobalTheory.CuspRep.IsStable (bdSub (E := E) (N := N) r ρ) := by
  rintro o φ ⟨hφ, p, hp, hpz, hpk⟩
  refine ⟨lo_act hφ o, p, hp, hpz, ?_⟩
  rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  have _ := hμ
  exact kl_act_lo μ 𝓕 h𝓕 hφ (hpk _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩) o

theorem re_le_of_mem {r : ℕ} {ρ : ℝ} {φ : Sm E N} (hφ : φ ∈ bdSub (E := E) (N := N) r ρ) {c : ℂ}
    (hc : c ∈ Exp r φ.1) : c.re ≤ ρ := by
  obtain ⟨-, p, -, hpz, hpk⟩ := hφ
  obtain ⟨F₀, hCT, F, hF, hF0, hFe⟩ := hc
  have hroot := kl_eigen (kl_span (hpk _ hCT) hF) hF0 hFe
  have := hpz _ hroot
  simpa [Complex.norm_exp] using this

theorem mem_bdSub {r : ℕ} (hr : 0 < r) (hrN : r < N) {ρ : ℝ} {φ : Sm E N} (hφ : IsAutForm φ)
    (hρ : ∀ c ∈ Exp r φ.1, c.re ≤ ρ) : φ ∈ bdSub (E := E) (N := N) r ρ := by
  obtain ⟨-, -, -, hDct⟩ := dict_holds E N
  obtain ⟨hct, huniq⟩ := hDct φ hφ r hr hrN
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    let _ : MeasurableSpace (BlockIx N r → Ad E) := _root_.borel _
    have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, h𝓕, e⟩ := hct
    obtain ⟨F, hF, -⟩ := ct_smooth E N r φ hφ.left hφ.level μ 𝓕 hμ h𝓕
    have e2 : An.ctn r φ.1 = F.1 := e.trans (funext fun g => (hF g).symm)
    intro g
    rw [e2]
    exact PDich.continuous_aT F r g
  obtain ⟨p, hp, hk, hroot⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) (fun u v => aT_add r u v) hcont
    (finTr_holds E N φ hφ r hr hrN _ hct)
  have hk' : Kl r 1 p (An.ctn r φ.1) := fun g => by
    simpa only [one_mul] using hk g
  refine ⟨⟨hφ.left, hφ.level⟩, p, hp, fun z hz => ?_, fun F hF => ?_⟩
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroot z hz
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (hρ c ⟨_, hct, F, hF, hF0, hFe⟩)
  · obtain ⟨a, -, rfl⟩ := huniq F hF
    exact (klSub r 1 p).smul_mem a hk'

end GlobalTheory.CompanionTheory.HullExp


open GlobalTheory.CompanionTheory.HullExp in
theorem GlobalTheory.CompanionTheory.HullExp.hullNonPos : PositivityTheory.Rg.BcB.E.E3.HullNonPos := by
  intro E _ _ _ N S hS φ hφ r hr hrN c hc
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have key : ∀ ψ ∈ S, ψ ∈ bdSub (E := E) (N := N) r (An.rho E N r) := fun ψ hψ =>
    mem_bdSub hr hrN (hS ψ hψ).1 fun c' hc' => by
      have := (hS ψ hψ).2 r hr hrN c' hc'
      rw [pE, sub_nonpos, div_le_iff₀ hd] at this
      rw [An.rho]
      linarith
  have hmem : φ ∈ bdSub (E := E) (N := N) r (An.rho E N r) :=
    (Submodule.mem_sInf.1 hφ) _ ⟨key, isStable_bdSub r _⟩
  have := re_le_of_mem hmem hc
  rw [pE, sub_nonpos, div_le_iff₀ hd]
  rw [An.rho] at this
  linarith

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSat2InvTConj
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open GlobalTheory.LFun.ConjPlace (invT dGL apply_heckeVec_shift Tj_invT Tj_shift_self map_mem_Ov_iff mem_iff_invT satEig_inv_mul satEig_zero)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ThetaSatPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {u w : Pl E}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem embT_cw (a : ℕ) (u : Pl E) (g : GLw a (GlobalTheory.ThetaSatake.cw u)) :
    embT a (GlobalTheory.ThetaSatake.cw u) g =
      embW a u (PhiU a _ * invT (GlobalTheory.ThetaSatake.cloc u) a g * (PhiU a _)⁻¹) := by
  change GlobalTheory.ThetaPull.thetaA E a (finGL E a (locGL E a (GlobalTheory.ThetaSatake.cw u) g)) = finGL E a (locGL E a u _)
  rw [GlobalTheory.ThetaPull.thetaA_finGL, GlobalTheory.ThetaSatake.theta_locGL, GlobalTheory.ThetaSatake.thetaGL_conj]

theorem invT_symm {K K' : Type} [Field K] [Field K'] (c : K ≃+* K') (n : ℕ) (g : GL (Fin n) K') :
    (invT c n).symm g = invT c.symm n g := rfl

end GlobalTheory.CompanionTheory.ThetaSatPair
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitAtOfValuation
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MuLocal

open _root_.Formalism.L2.Host GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnitAt_of_valuation (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (h : ValuativeRel.valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1) : IsUnitAt w x := by
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have h1 := GlobalTheory.SmGL.ord_eq_zero_iff.2 h
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at h1
  rw [IsUnitAt, ← WithZero.exp_log h0, h1, WithZero.exp_zero]

theorem loc_eq_unrChar {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) :
    χ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (χ.val w) :=
  GlobalTheory.PrinSat.eq_unrChar_of_ord (fun x hx => h x (isUnitAt_of_valuation w x hx)) (GlobalTheory.PrinSat.ord_unif w)

theorem loc_pow (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) (x : (w.adicCompletion E)ˣ) :
    (χ ^ k).loc w x = χ.loc w x ^ k := by
  simp [HChar.loc]

theorem loc_mul_loc_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : GlobalTheory.BCT.IsMu μ e) (w : HeightOneSpectrum (𝓞 E))
    (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ) :
    μ.loc (GlobalTheory.ThetaSatake.cw w) x * μ.loc w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) = 1 := by
  have h1 := GlobalTheory.BCT.MuProps.mu_mul_conj h (Neutral.B1.localIdele E _ x)
  rw [GlobalTheory.PolChar.ideleConj_eq, GlobalTheory.ThetaPull.conjAd_localIdele] at h1
  exact h1

theorem isUnitAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnitAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnitAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

theorem isUnifAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnifAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnifAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

end GlobalTheory.CompanionTheory.MuLocal


open GlobalTheory.CompanionTheory.MuLocal Formalism.L2.Host GlobalTheory.CuspRep in
theorem GlobalTheory.CompanionTheory.MuLocal.muLoc_holds : PositivityTheory.Rg.BcB.F.RS.MuLoc := by
  intro E _ _ _ _ μ e w hμ hun
  refine ⟨loc_eq_unrChar hun, fun k => ⟨fun x hx => ?_, ?_⟩, fun u _ hu => ?_⟩
  · rw [loc_pow, hun x hx, one_pow]
  · rw [HChar.val, HChar.locK, MonoidHom.comp_apply, loc_pow]
    rfl
  · obtain rfl := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hu
    have hc := loc_mul_loc_conj hμ w
    refine ⟨fun x hx => ?_, ?_⟩
    · have h2 := hc x
      rw [hun _ (isUnitAt_conj w x hx), mul_one] at h2
      exact h2
    · have h2 := hc (atFin (GlobalTheory.ThetaSatake.cw w) (unif (GlobalTheory.ThetaSatake.cw w)))
      rw [μ.val_eq hun _ (isUnifAt_conj w _ (unif_spec _))] at h2
      exact eq_inv_of_mul_eq_one_left h2

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentShiftInvariance
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentShiftInvariance
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting.ShiftP
section Generic
variable {R : Type} [CommRing R] {r t n : ℕ}

theorem upperUnipotent_mul (hn : r + t = n) (y y' : Matrix (Fin r) (Fin t) R) :
    bl hn 1 y 0 1 * bl hn 1 y' 0 1 = bl hn 1 (y + y') 0 1 := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem upperUnipotent_zero (hn : r + t = n) : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem det_bl_one (hn : r + t = n) (y : Matrix (Fin r) (Fin t) R) : (bl hn 1 y 0 1).det = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

end Generic

variable {D : D7} {n t : ℕ} {B W : HSp D}

def shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by rw [upperUnipotent_mul, add_neg_cancel, upperUnipotent_zero]
  inv_val := by rw [upperUnipotent_mul, neg_add_cancel, upperUnipotent_zero]

theorem det_shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) :
    Matrix.GeneralLinearGroup.det (shear (D := D) hn y : GL (Fin n) (AE D)) = 1 :=
  Units.ext (det_bl_one hn y)

theorem integral_shear {r : ℕ} (hn : r + t = n) (y : Mx D r t) {m : ℕ} (μ : Measure (Mx D m n)) (hμ : μ.IsAddHaarMeasure)
    (f : Mx D m n → ℂ) : ∫ U, f (mm U (bl hn 1 y 0 1)) ∂μ = ∫ U, f U ∂μ := by
  have h := GlobalTheory.CompanionTheory.IwaAd.integral_mul_right m μ hμ (shear hn y) f
  rw [det_shear, map_one, one_npow, one_mul] at h
  exact h

end GlobalTheory.CompanionTheory.ColumnSplitting.ShiftP

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem shift : Shift := by
  intro D n t B W d hn I Φ y a
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have e := ShiftP.integral_shear hn y I.μ₁ hf.1
    (fun U => projS I.νK Φ (d.jX ⬝ U + d.j0 ⬝ (mm a (bl hn 1 y 0 1))))
  simp only [ikp, ikS]
  rw [← e]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [projS]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [mm, Matrix.mul_assoc, Matrix.add_mul]

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentShiftInvarianceStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_shift_invariance : Shift := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.shift | exact GlobalTheory.CompanionTheory.ColumnSplitting.shift | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.shift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlobalHermitianLocalApproximation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlobalHermitianLocalApproximation
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp

open GlobalTheory.EmbChart (tensAt compFin_tensAt)

theorem compFin_tensAt_ne_place {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (y : Fv F v ⊗[F] E) :
    compFin F E u (tensAt E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    change (evalV F u (singleFin v a)) ⊗ₜ[F] x = 0
    rw [evalV_singleFin_ne h, TensorProduct.zero_tmul]

theorem compInf_tensAt_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    compInf F E w (tensAt E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    change (evInf F w (GlobalTheory.EmbChart.atPlace v a)) ⊗ₜ[F] x = 0
    rw [show evInf F w (GlobalTheory.EmbChart.atPlace v a) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), TensorProduct.zero_tmul]

theorem cA_tensAt (D : D7) (v : Pl D) (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    cA D (tensAt D.host.E v y) = tensAt D.host.E v (sigR (Fv D.host.F v) D.sp.cm.sig y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem splitProj_sigR (D : D7) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    splitProj τ (sigR (Fv D.host.F v) D.sp.cm.sig y) = splitProj (τ.comp D.sp.cm.sig) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem exists_herm_at (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (X : Matrix (Fin n) (Fin n) (Fv D.host.F v)) :
    ∃ x : hermA D n, (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) ∧
      (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) ∧ tauC τ x.1 = X ∧
      ((∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) →
        ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) := by
  have h := isCMExt_host D
  set M := splitPairMat h τ X Xᵀ with hM
  have p1 : ∀ i j, splitProj τ (M i j) = X i j := fun i j => by
    have := congrArg Prod.fst ((splitAlgEquiv h τ).apply_symm_apply (X i j, Xᵀ i j))
    rwa [splitAlgEquiv_apply] at this
  have p2 : ∀ i j, splitProj (τ.comp D.sp.cm.sig) (M i j) = X j i := fun i j => by
    have := congrArg Prod.snd ((splitAlgEquiv h τ).apply_symm_apply (X i j, Xᵀ i j))
    rwa [splitAlgEquiv_apply] at this
  have hs : ∀ i j, sigR (Fv D.host.F v) D.sp.cm.sig (M j i) = M i j := fun i j => by
    apply (splitAlgEquiv h τ).injective
    rw [splitAlgEquiv_apply, splitAlgEquiv_apply, splitProj_sigR, splitProj_comp_sigR h, p1, p2, p1, p2]
  have hc : ∀ i j, cv D v (tensAt D.host.E v (M i j)) = M i j := fun i j => compFin_tensAt v _
  refine ⟨⟨Matrix.of fun i j => tensAt D.host.E v (M i j), ?_⟩, ?_, ?_, ?_, ?_⟩
  · change adj _ = _
    ext i j
    change cA D (tensAt D.host.E v (M j i)) = tensAt D.host.E v (M i j)
    rw [cA_tensAt, hs]
  · intro w i j
    exact compInf_tensAt_eq_zero w v _
  · intro v' hv i j
    exact compFin_tensAt_ne_place hv _
  · refine Matrix.ext fun i j => ?_
    change splitProj τ (cv D v (tensAt D.host.E v (M i j))) = X i j
    rw [hc, p1]
  · intro hX i j
    change cv D v (tensAt D.host.E v (M i j)) ∈ _
    rw [hc, mem_intLoc_iff_split h τ, p1, p2]
    exact ⟨hX i j, hX j i⟩

end GlobalTheory.CompanionTheory.Jp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlobalHermitianLocalApproximationStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_hermitian_local_approximation : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (X : Matrix (Fin n) (Fin n) (Fv D.host.F v)), ∃ x : hermA D n, (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) ∧ (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) ∧ tauC τ x.1 = X ∧ ((∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.exists_herm_at | exact GlobalTheory.CompanionTheory.Jp.exists_herm_at | (intros; apply GlobalTheory.CompanionTheory.Jp.exists_herm_at <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatVMapMulChi
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Rs.SatakeVectors PositivityTheory.Rg.Rs.SatakeVectors.SatakeVectorEventually PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JoinSatPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem satV_of_comp {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin N) (w.adicCompletion E))} (h : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hs : HasSatGL w σ.ρ B) : SatV V w B := by
  have hmem : ∀ ψ ∈ V, ψ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [iSup_range_eq hV w σ h]; exact hψ
  refine ⟨?_, fun ψ hψ hψK hψ0 =>
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hs (fun f : MapsD V w σ => f.1) (fun f => f.2.2)
      (hmem ψ hψ) (GlobalTheory.LGrp.mem_fixed.2 hψK) hψ0⟩
  obtain ⟨x, hx⟩ := hs.exists_vec
  obtain ⟨f, h0, hfV, hf⟩ := h
  haveI := σ.irred
  have hi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero
      (f.intertwiningMap_of_isIntertwiningMap σ.ρ ((finRep E N).comp (locGL E N w)) hf) with hi | hz
    · exact hi
    · exact absurd (LinearMap.ext fun s => DFunLike.congr_fun hz s) h0
  exact ⟨f x, hfV x, hx.map f hf fun e => hx.1 (hi (by rw [e, map_zero]))⟩

theorem hasSat_of_satV {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin N) (w.adicCompletion E))} (h : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hs : SatV V w B) : HasSatGL w σ.ρ B := by
  obtain ⟨⟨φ, hφ, hφs⟩, -⟩ := hs
  have hfix : ∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ := fun k hk =>
    GlobalTheory.LGrp.mem_fixed.1 hφs.2.1 k hk
  have hmem : φ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := by
    rw [iSup_range_eq hV w σ h]; exact hφ
  obtain ⟨v, hv0, hv⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E N).comp (locGL E N w)) σ.ρ σ.irred
    (fun f : MapsD V w σ => f.1) (fun f => f.2.2) (KGL w (n := N) : Set _) φ hφs.1 hfix hmem
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w (n := N)) :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩
  obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hsph
  have e : B' = B := ((satV_of_comp hV h hB').2 φ hφ hfix hφs.1).unique hφs
  exact e ▸ hB'

theorem satV_map_mulChi {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    {χ : HChar E} (hχ : χ.UnrAt w) (h : SatV V w B) :
    SatV (V.map (mulChi m χ).toLinearMap) w (B.map (· * χ.val w)) := by
  have L := satLike_map_mulChi hχ (satLike_of_satV h)
  refine ⟨?_, L⟩
  obtain ⟨⟨φ, hφ, hs⟩, -⟩ := h
  have hm : (mulChi m χ) φ ∈ V.map (mulChi m χ).toLinearMap := Submodule.mem_map_of_mem hφ
  refine ⟨_, hm, L _ hm (fun k hk => ?_) fun e => hs.1 ((mulChi m χ).injective (by rw [e, map_zero]))⟩
  rw [finRep_mulChi, hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one, one_smul]
  exact congrArg _ (GlobalTheory.LGrp.mem_fixed.1 hs.2.1 k hk)

def PartSat (w : HeightOneSpectrum (𝓞 E)) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (B : Multiset ℂˣ) : Prop :=
  SatV x.2 w B

variable {n a b : ℕ}

theorem pre_sat_iff (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) :
    D.Sat w B ↔ ∃ l : List (Multiset ℂˣ), List.Forall₂ (PartSat w) (parts D) l ∧ l.sum = B := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨List.ofFn c, ?_, List.sum_ofFn⟩
    refine List.forall₂_iff_get.2 ⟨by simp [parts], fun i h₁ h₂ => ?_⟩
    simp only [parts, List.get_eq_getElem, List.getElem_ofFn]
    exact satV_of_comp (D.discrete _) (D.loc _ w) (hc _).2
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hlen, hg⟩ := List.forall₂_iff_get.1 hl
    have hlen' : D.c = l.length := by simpa [parts] using hlen
    have hS : ∀ i : Fin D.c, HasSatGL w (D.σ i w).ρ (l.get (i.cast hlen')) := fun i => by
      have := hg i.1 (by simp [parts]) (by simpa [hlen'] using i.2)
      simp only [parts, List.get_eq_getElem, List.getElem_ofFn] at this
      exact hasSat_of_satV (D.discrete i) (D.loc i w) this
    refine ⟨fun i => l.get (i.cast hlen'), fun i => ⟨(hS i).1, hS i⟩, ?_⟩
    have e : List.ofFn (fun i : Fin D.c => l.get (i.cast hlen')) = l :=
      List.ext_get (by simp [hlen']) fun i h₁ h₂ => by simp
    rw [← List.sum_ofFn, e]

theorem sum_map_map (f : ℂˣ → ℂˣ) (l : List (Multiset ℂˣ)) :
    (l.map (Multiset.map f)).sum = l.sum.map f := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem forall₂_tw {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    {p : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {l : List (Multiset ℂˣ)} (h : List.Forall₂ (PartSat w) p l) :
    List.Forall₂ (PartSat w) (p.map (twPart χ)) (l.map (Multiset.map (· * χ.val w))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h _ ih => exact List.Forall₂.cons (satV_map_mulChi hχ h) ih

theorem joinSat : PositivityTheory.Rg.BcB.F.RS.JoinSat := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pb D w Ba Bb hJ h1 h2 sa sb
  obtain ⟨la, fa, rfl⟩ := (pre_sat_iff Pa w Ba).1 sa
  obtain ⟨lb, fb, rfl⟩ := (pre_sat_iff Pb w Bb).1 sb
  refine (pre_sat_iff D w _).2 ⟨la.map (Multiset.map (· * χ₁.val w)) ++ lb.map (Multiset.map (· * χ₂.val w)), ?_, ?_⟩
  · rw [hJ]
    exact List.rel_append (forall₂_tw h1 fa) (forall₂_tw h2 fb)
  · rw [List.sum_append, sum_map_map, sum_map_map]

end GlobalTheory.CompanionTheory.JoinSatPf

end
end
