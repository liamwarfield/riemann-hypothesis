module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL.UnitaryOrder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hasCentralChar_nu (x : IrrGL (k := k)) {ω : kˣ →* ℂˣ} (h : HasCentralChar x.rep ω) (s : ℂ) :
    HasCentralChar (x.nu s).rep (ω * absPow k s ^ x.1) := by
  have h1 := hasCentralChar_twist h (absPow k s)
  rw [Fintype.card_fin] at h1
  exact hasCentralChar_of_equiv (x.twEquiv _ _) h1

theorem norm_eq_one_of_isUnitarisable {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    {ρ : Representation ℂ G X} (hU : IsUnitarisable ρ) {g : G} {c : ℂ} (hc : ∀ v, ρ g v = c • v) : ‖c‖ = 1 := by
  obtain ⟨B, -, hp, hi⟩ := hU
  obtain ⟨v, hv⟩ := exists_ne (0 : X)
  have h := hi g v v
  have h0 : B v v ≠ 0 := fun e => by simpa [e] using hp v hv
  rw [hc, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Complex.mul_conj, mul_eq_right₀ h0] at h
  have h2 : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

theorem log_norm_mul_absPow (ω : kˣ →* ℂˣ) (t : ℝ) (d : ℕ) (z : kˣ) :
    Real.log ‖(((ω * absPow k (t : ℂ) ^ d) z : ℂˣ) : ℂ)‖ =
      Real.log ‖(ω z : ℂ)‖ + d * t * Real.log (nabs k z) := by
  have hz := nabs_pos' k z
  have hω : ‖(ω z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 (ω z).ne_zero
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, val_absPow_ofReal,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hz.le _),
    Real.log_mul hω (pow_ne_zero _ (Real.rpow_pos_of_pos hz _).ne'), Real.log_pow, Real.log_rpow hz]
  ring

theorem sum_range_mul_two (l : ℕ) : (∑ i ∈ Finset.range l, (i : ℝ)) * 2 = l * ((l : ℝ) - 1) := by
  induction l with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

theorem log_norm_centralChar {δ : IrrGL (k := k)} {Δ : Segment k} (hL : IsLSeg Δ δ.rep) (hU : IsUnitarisable δ.rep)
    {ω : kˣ →* ℂˣ} (hω : HasCentralChar Δ.first.rep ω) (z : kˣ) :
    Real.log ‖(ω z : ℂ)‖ = -((Δ.d : ℝ) * ((Δ.len : ℝ) - 1) / 2) * Real.log (nabs k z) := by
  obtain ⟨hd, hi, f, hf, -⟩ := hL
  have hterm : ∀ a : Fin Δ.len,
      HasCentralChar (Δ.term a).rep (ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d) := fun a => by
    have h := hasCentralChar_nu Δ.first hω ((a : ℕ) : ℂ)
    rw [Complex.ofReal_natCast]
    exact h
  have hsc : ∀ v, δ.rep (GeneralLinearGroup.scalar (Fin δ.1) z) v =
      (∏ a : Fin Δ.len, (((ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d) z : ℂˣ) : ℂ)) • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf v
    have h1 := GlobalTheory.BoundaryMaps.multiProd_scalar (stdBlocks (fun a => (Δ.term a).1) hd)
      (fun a => (Δ.term a).rep) _ hterm z w
    rw [← f.isIntertwining]
    exact (congrArg f h1).trans (map_smul f _ _)
  haveI := Model.nontrivial_of_isIrreducible hi
  have hc := congrArg Real.log (norm_eq_one_of_isUnitarisable hU hsc)
  rw [norm_prod, Real.log_one, Real.log_prod fun a _ => norm_ne_zero_iff.2 (Units.ne_zero _)] at hc
  simp only [log_norm_mul_absPow] at hc
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) Δ.len] at hc
  have hS := sum_range_mul_two Δ.len
  have hl : (Δ.len : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Δ.len_pos.ne'
  apply mul_left_cancel₀ hl
  linear_combination hc - ((Δ.d : ℝ) * Real.log (nabs k z) / 2) * hS

theorem add_one_le_of_precedes (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k) (hL : IsLSeg Δ δ.rep) (hU : IsUnitarisable δ.rep) (hL' : IsLSeg Δ' δ'.rep)
    (hU' : IsUnitarisable δ'.rep) (x y : ℝ) (hP : (Δ.nu x).Precedes (Δ'.nu y)) : x + 1 ≤ y := by
  obtain ⟨⟨-, -, hnsub⟩, j, hj, hfirst⟩ := hP
  have hf : Δ'.first.nu (y : ℂ) = (Δ.first.nu (x : ℂ)).nu (j : ℂ) := hfirst
  have hρ' : Δ'.first = Δ.first.nu (((x + j - y : ℝ)) : ℂ) := by
    have h1 := congrArg (fun r => r.nu (-(y : ℂ))) hf
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h1
    rw [h1]
    congr 1
    push_cast
    ring
  have hd : Δ'.d = Δ.d := congrArg Sigma.fst hρ'
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar Δ.first.2.rep.smooth Δ.first.2.rep.irr
  have hω' : HasCentralChar Δ'.first.rep (ω * absPow k (((x + j - y : ℝ)) : ℂ) ^ Δ.first.1) := by
    rw [hρ']
    exact hasCentralChar_nu _ hω _
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hne : nabs k ϖ ≠ 1 := fun e => uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have hL0 : Real.log (nabs k ϖ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) hne
  have hA := log_norm_centralChar hL hU hω ϖ
  have hA' := log_norm_centralChar hL' hU' hω' ϖ
  rw [log_norm_mul_absPow, hd] at hA'
  have hdL : (Δ.d : ℝ) * Real.log (nabs k ϖ) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 Δ.d_pos.ne') hL0
  have ht : x + j - y = ((Δ.len : ℝ) - Δ'.len) / 2 := by
    apply mul_left_cancel₀ hdL
    have e1 : (Δ.first.1 : ℝ) = Δ.d := rfl
    rw [e1] at hA'
    linear_combination hA' - hA
  have hlen : Δ.len < j + Δ'.len := by
    by_contra hcon
    push_neg at hcon
    apply hnsub
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hw
    refine Segment.mem_carrier.2 ⟨j + a, ?_, ?_⟩
    · have ha' : a < Δ'.len := ha
      show j + a < Δ.len
      omega
    · rw [hfirst, IrrGL.nu_nu]
      push_cast
      rfl
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hl1 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast hlen
  linarith

end GlobalTheory.LocGL.UnitaryOrder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLeStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y := by
  first | exact @GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes | exact GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes | (intros; apply GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix GlobalTheory.PRep GlobalTheory.Published GlobalTheory.UnitaryBC
open GlobalTheory.CuspRep.LocEx

namespace GlobalTheory.DiscLocEx

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def opD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (o : Op E a) : Module.End ℂ V := (act o).restrict (hV o)

def finPartD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) : Representation ℂ (GL (Fin a) (Af E)) V :=
  GlobalTheory.PRep.sub (finRep E a) V fun k => hV (.fin k)

def locRepD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E)) :
    Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
  (finPartD hV).comp (locGL E a w)

theorem isSmooth_finPartD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ) :
    IsSmooth (finPartD hV) := fun φ => by
  convert (ha _ φ.2).level using 1
  ext k
  exact Subtype.ext_iff

theorem isSmooth_locRepD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ)
    (w : HeightOneSpectrum (𝓞 E)) : IsSmooth (locRepD hV w) := fun φ =>
  (isSmooth_finPartD hV ha φ).preimage (CuspSub.continuous_locGL w)

theorem exists_scalarD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem nullPart_opD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (o : Op E a) {x : V} (hx : x ∈ nullPart (locRepD hV w) K) : opD hV o x ∈ nullPart (locRepD hV w) K := by
  cases o with
  | fin k =>
    have h1 := nullPart_act _ K (GeneralLinearGroup.map (pLoc E w) k) (nullPart_comm _ K
      (finPartD hV ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
      simp only [locRepD, MonoidHom.comp_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        LocUniq.comm_locGL w (map_pLoc_inv_mul w k)]) hx)
    rwa [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
  | cpt k =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem eq_bot_of_fixedD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    {K : Subgroup (GL (Fin a) (w.adicCompletion E))} (hK : IsCompact (K : Set (GL (Fin a) (w.adicCompletion E))))
    {φ : V} (h0 : φ ≠ 0) (hφ : φ ∈ fixed (locRepD hV.stable w) K) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, locRepD hV.stable w g v ∈ W) (h : W ⊓ fixed (locRepD hV.stable w) K = ⊥) : W = ⊥ := by
  have hi := Submodule.map_injective_of_injective V.injective_subtype
  rcases hV.irred ((nullPart (locRepD hV.stable w) K).map V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, nullPart_opD hV.stable w K o hx, rfl⟩) with h1 | h1
  · have h2 : nullPart (locRepD hV.stable w) K = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    exact le_bot_iff.1 (h2 ▸ le_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK W hW h)
  · have h2 : nullPart (locRepD hV.stable w) K = ⊤ := hi (h1.trans (Submodule.map_subtype_top _).symm)
    exact absurd (eq_zero_of_mem_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK hφ (h2 ▸ Submodule.mem_top)) h0

def typePartD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) : Submodule ℂ V where
  carrier := {ψ | (∀ k ∈ L, GeneralLinearGroup.map (pLoc E w) k = 1 → finPartD hV k ψ = ψ) ∧
    ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k h1 h2 => by rw [map_add (f := _), hx.1 k h1 h2, hy.1 k h1 h2],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => map_zero _, fun _ => zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k h1 h2 => by rw [map_smul, hx.1 k h1 h2],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem typePartD_act {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (g : GL (Fin a) (w.adicCompletion E))
    (x : V) (hx : x ∈ typePartD hV w L ρ) : locRepD hV w g x ∈ typePartD hV w L ρ := by
  refine ⟨fun k h1 h2 => ?_, fun y => ?_⟩
  · rw [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, LocUniq.comm_locGL w h2, map_mul,
      Module.End.mul_apply, hx.1 k h1 h2]
  · convert hx.2 (y * finGL E a (locGL E a w g)) using 2 with k
    change x.1.1 (y * infGL E a _ * finGL E a _) = x.1.1 (y * finGL E a _ * infGL E a _)
    rw [mul_assoc, mul_assoc, infGL_comm]

theorem finiteDimensional_typePartD (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E))
    {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {ρ : Representation ℂ (Kinf E a) W}
    (hρ : AutFin.IsContRep ρ) (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (hK : IsOpen (K : Set (GL (Fin a) (w.adicCompletion E)))) :
    FiniteDimensional ℂ ↥(typePartD hV.stable w L ρ ⊓ fixed (locRepD hV.stable w) K) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ V, cap τ u φ = c • φ := fun τ u =>
    exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w)))
    (hL.inter ((hK.inter (hL.preimage (CuspSub.continuous_locGL w))).preimage (continuous_map_pLoc w))) W ρ hρ c
  refine FiniteDimensional.of_injective ((V.subtype ∘ₗ (typePartD hV.stable w L ρ ⊓
    fixed (locRepD hV.stable w) K).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms
      (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w))) ρ c))
    fun v => Submodule.subset_span ⟨hV.aut _ v.1.2, fun k hk => ?_, v.2.1.2, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  have h1 := v.2.1.1 _ (L.mul_mem (L.inv_mem hk.2.2) hk.1) (map_pLoc_inv_mul w k)
  have h2 := mem_fix.1 v.2.2 _ hk.2.1
  have h3 : finPartD hV.stable k v.1 = v.1 := by
    rw [← mul_inv_cancel_left (locGL E a w (GeneralLinearGroup.map (pLoc E w) k)) k, map_mul, Module.End.mul_apply, h1]
    exact h2
  exact congrArg Subtype.val h3

theorem exists_irred_sub (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E)) :
    ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), (∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧
      ∀ g v, f (σ.ρ g v) = locRepD hV.stable w g (f v)) ∧ IsAdmissible σ.ρ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have h0' : (⟨φ, hφ⟩ : V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hL : IsOpen (stab (finPartD hV.stable) ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) :=
    isSmooth_finPartD hV.stable hV.aut _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have : FiniteDimensional ℂ (orbSpan φ) := (hV.aut φ hφ).kfin
  refine exists_irred (isSmooth_locRepD hV.stable hV.aut w) ho (eq_bot_of_fixedD hV w hc h0' (mem_fix.2 hK))
    (typePartD hV.stable w (stab (finPartD hV.stable) ⟨φ, hφ⟩) (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)))
    (typePartD_act hV.stable w _ _)
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, ⟨fun k hk _ => hk, ?_⟩, h0'⟩)
    (finiteDimensional_typePartD h hV w hL (isContRep_sub _ _))
  exact AutFinGL.type_of_map (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)) (orbSpan φ).subtype (fun _ _ => rfl)
    ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩

end GlobalTheory.DiscLocEx


open GlobalTheory.DiscSpec GlobalTheory.SmGL in
theorem GlobalTheory.DiscLocEx.exists_isLocCompGL : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (N : ℕ), ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V →
    ∀ w : HeightOneSpectrum (𝓞 E), ∃ σ' , IsLocCompGL V w σ' := by
  intro h E _ _ _ N V hV w
  obtain ⟨σ, ⟨f, hf0, hf⟩, -⟩ := GlobalTheory.DiscLocEx.exists_irred_sub h hV w
  refine ⟨σ, V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun g v => congrArg Subtype.val (hf g v)⟩
  exact LinearMap.congr_fun e v
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponentStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteAutomorphicRepGL_exists_localComponent : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ w : HeightOneSpectrum (𝓞 E), ∃ σ' , IsLocCompGL V w σ' := by
  first | exact @GlobalTheory.DiscLocEx.exists_isLocCompGL | exact GlobalTheory.DiscLocEx.exists_isLocCompGL | (intros; apply GlobalTheory.DiscLocEx.exists_isLocCompGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

noncomputable section

namespace GlobalTheory.NuShift

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpChar_lpTw (x y : WD h) (s : ℝ) : (x.lpTw s).lpChar y = (x.lpChar y).lpTw s := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpTw_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
  · simp only [WDRep.tensor_ρ, WDRep.tw_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left]
  · rfl

theorem lpTw_lpZero (s : ℝ) : (WD.lpZero (h := h)).lpTw s = WD.lpZero (h := h) := by
  rw [WD.lpZero, WD.lpTw_mk]
  exact WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩

theorem sumList_lpTw (l : List (WD h)) (s : ℝ) :
    sumList (l.map fun x => x.lpTw s) = (sumList l).lpTw s := by
  induction l with
  | nil => exact (lpTw_lpZero s).symm
  | cons x l ih =>
    show WD.lpSum _ (sumList _) = (WD.lpSum x (sumList l)).lpTw s
    rw [ih, WD.lpTw_sum]

end GlobalTheory.NuShift

namespace GlobalTheory

open GlobalTheory.NuShift

theorem lpSum_segments_nu : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (l : List (Segment (w.adicCompletion E))) (c : ℝ),
      sumList ((l.map fun Γ => Γ.nu (c : ℂ)).map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)) =
        (sumList (l.map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))).lpTw c := by
  intro E Ω _ _ _ _ _ A w
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h rc hrc l c
  obtain ⟨a, ha, ε, -, L⟩ := hrc
  rw [← sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  rw [L.nu_eq, WD.lpTw_add, add_comm, ← WD.lpTw_add, lpChar_lpTw]
  rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh MeasureTheory Matrix

namespace GlobalTheory.DiscreteUnit

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [Countable Γ]

theorem lintegral_lt_top {μ μ' : Measure G} [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {F F' : Set G}
    (hF : IsFundamentalDomain Γ F μ) (hF' : IsFundamentalDomain Γ F' μ') {φ : G → ENNReal}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (h : ∫⁻ g in F', φ g ∂μ' < ⊤) : ∫⁻ g in F, φ g ∂μ < ⊤ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hF2 : IsFundamentalDomain Γ F' μ := hF'.mono (Measure.absolutelyContinuous_isHaarMeasure μ μ')
  rw [hF.setLIntegral_eq hF2 φ fun γ g => hφ γ γ.2 g, e, Measure.restrict_smul, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h

theorem integral_mul_right {μ : Measure G} [μ.IsHaarMeasure] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {φ : G → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) {x : G} (hx : Measure.modularCharacter x = 1) :
    ∫ g in F, φ (g * x) ∂μ = ∫ g in F, φ g ∂μ := by
  have hm : MeasurePreserving (fun g => g * x) μ μ :=
    ⟨measurable_mul_const x, by rw [GlobalTheory.LevelUnimod.map_mul_right_eq, hx, one_smul]⟩
  have hF2 : IsFundamentalDomain Γ ((fun g => g * x) ⁻¹' F) μ :=
    hF.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc γ.1 g x
  rw [hF.setIntegral_eq hF2 (f := fun g => φ (g * x)) fun γ g => by
    change φ (γ.1 * g * x) = _
    rw [mul_assoc, hφ γ γ.2]]
  exact hm.setIntegral_preimage_emb (MeasurableEquiv.mulRight x).measurableEmbedding φ F

theorem isUnitarisable_of_embedding {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (ι : H → G) (hι : ∀ h, Measure.modularCharacter (ι h) = 1) (f : X →ₗ[ℂ] (G → ℂ)) (hf : Function.Injective f)
    (hc : ∀ v, Continuous (f v)) (hl : ∀ v, ∀ γ ∈ Γ, ∀ g, f v (γ * g) = f v g)
    (h2 : ∀ v, ∃ (μ : Measure G) (F : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ F μ ∧
      ∫⁻ g in F, ‖f v g‖ₑ ^ 2 ∂μ < ⊤)
    (hρ : ∀ h v g, f (ρ h v) g = f v (g * ι h)) : IsUnitarisable ρ := by
  obtain ⟨μ, F, hμ, hF, -⟩ := h2 0
  have hm : ∀ v, MemLp (f v) 2 (μ.restrict F) := fun v => by
    obtain ⟨μ', F', hμ', hF', h⟩ := h2 v
    have h3 := lintegral_lt_top hF hF' (fun γ hγ g => by rw [hl v γ hγ g]) h
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    · simpa using h3
    · exact (hc v).aestronglyMeasurable
  have hi : ∀ v w, Integrable (fun g => f v g * starRingEnd ℂ (f w g)) (μ.restrict F) := fun v w =>
    (hm v).integrable_mul (hm w).star
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∫ g in F, f v g * starRingEnd ℂ (f w g) ∂μ)
    (fun v v' w => ?_) (fun c v w => ?_) (fun v w w' => ?_) (fun c v w => ?_), fun v w => ?_, fun v hv => ?_,
    fun h v w => ?_⟩
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [add_mul]
  · simp [mul_assoc, integral_const_mul]
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [mul_add]
  · simp [mul_left_comm _ (starRingEnd ℂ c), integral_const_mul]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← integral_conj]
    simp [mul_comm]
  · simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    have hi2 : Integrable (fun g => Complex.normSq (f v g)) (μ.restrict F) := by
      simpa [Complex.mul_conj] using (hi v v).re
    refine (integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hi2).2 (pos_iff_ne_zero.2 fun h0 => hv ?_)
    have ho : IsOpen (Function.support fun g => Complex.normSq (f v g)) :=
      (Complex.continuous_normSq.comp (hc v)).isOpen_support
    rw [Measure.restrict_apply ho.measurableSet] at h0
    have h4 := hF.measure_zero_of_invariant _ (fun γ => by
      ext g
      rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
      change Complex.normSq (f v ((γ⁻¹ : Γ).1 * g)) ≠ 0 ↔ _
      rw [hl v _ (γ⁻¹).2]) h0
    have h5 := Function.support_eq_empty_iff.1 (ho.measure_eq_zero_iff μ |>.1 h4)
    refine hf (funext fun g => ?_)
    rw [map_zero]
    exact Complex.normSq_eq_zero.1 (congrFun h5 g)
  · simp only [LinearMap.mk₂'ₛₗ_apply, hρ]
    exact integral_mul_right hF (φ := fun g => f v g * starRingEnd ℂ (f w g))
      (fun γ hγ g => by rw [hl v γ hγ, hl w γ hγ]) (hι h)

end General

def transInv (A : Type) [CommRing A] (n : ℕ) : GL (Fin n) A ≃* GL (Fin n) A where
  toFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  invFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  left_inv g := Units.ext (transpose_transpose _)
  right_inv g := Units.ext (transpose_transpose _)
  map_mul' g h := Units.ext (by
    change ((g * h)⁻¹).valᵀ = (g⁻¹).valᵀ * (h⁻¹).valᵀ
    rw [← transpose_mul, _root_.mul_inv_rev, Units.val_mul])

theorem continuous_transInv (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) :
    Continuous (transInv A n) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem cornerGL_transInv {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (s : R →ₙ+* S) (g : GL (Fin n) R) :
    cornerGL n s (transInv R n g) = transInv S n (cornerGL n s g) := by
  ext i j
  change (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((g⁻¹).val j i) =
    (1 : Matrix (Fin n) (Fin n) S) j i - s ((1 : Matrix (Fin n) (Fin n) R) j i) + s ((g⁻¹).val j i)
  simp only [Matrix.one_apply, eq_comm]

theorem modular_eq_one {k S : Type} [Field k] [Infinite k] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {n : ℕ}
    [LocallyCompactSpace (GL (Fin n) S)] [SecondCountableTopology (GL (Fin n) S)] (ι : GL (Fin n) k →* GL (Fin n) S)
    (h : ∀ g, ι (transInv k n g) = transInv S n (ι g)) (g : GL (Fin n) k) : Measure.modularCharacter (ι g) = 1 := by
  borelize (GL (Fin n) S)
  refine GlobalTheory.gl_character_eq_one_of_transpose_inv _ _ (Measure.modularCharacter.comp ι) (fun g g' e => ?_) g
  obtain rfl : g' = transInv _ n g := Units.ext e
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h]
  exact GlobalTheory.LevelUnimod.modular_aut _ (continuous_transInv _ n) (continuous_transInv _ n) _

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem countable_latticeGL : Countable (latticeGL E N) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin N) (Fin N) E) := inferInstanceAs (Countable (Fin N → Fin N → E))
  haveI : Countable (GL (Fin N) E) := Units.val_injective.countable
  let f : FreeGroup (Option (GL (Fin N) E)) →* GA E N :=
    FreeGroup.lift fun o => o.elim (splitCentre E N 1) (ratGL E N)
  have h : latticeGL E N ≤ f.range := sup_le
    (by rintro _ ⟨γ, rfl⟩; exact ⟨.of (some γ), FreeGroup.lift_apply_of⟩)
    (Subgroup.zpowers_le.2 ⟨.of none, FreeGroup.lift_apply_of⟩)
  haveI : Countable (FreeGroup (Option (GL (Fin N) E))) := Quot.mk_surjective.countable
  exact ((Set.countable_range f).mono h).to_subtype

theorem left_latticeGL {φ : Sm E N} (h : IsAutForm φ) (h' : IsSqInt φ.1) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by
    intro x hx
    obtain ⟨γ, rfl⟩ := (show x ∈ (ratGL E N).range from hx)
    exact h.left γ) (Subgroup.zpowers_le.2 (h'.1 1))
  exact this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitarisable_of_isLocCompGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ)
    (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : LocIrr w N),
    IsLocCompGL V w σ → IsUnitarisable σ.ρ := by
  intro E _ _ _ N V hV w σ ⟨f, h0, hf, hρ⟩
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := countable_latticeGL (E := E) (N := N)
  haveI : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  have hinj : Function.Injective f := by
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hρ, hv, map_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0
  refine isUnitarisable_of_embedding (Γ := latticeGL E N) σ.ρ (fun g => finGL E N (locGL E N w g)) (fun g => ?_)
    ((Sm E N).subtype.comp f) (Subtype.val_injective.comp hinj)
    (fun v => GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E N (f v) (hV.aut _ (hf v)).level)
    (fun v => left_latticeGL (hV.aut _ (hf v)) (hV.sqInt _ (hf v))) (fun v => (hV.sqInt _ (hf v)).2)
    fun g v x => congrFun (congrArg Subtype.val (hρ g v)) x
  exact modular_eq_one ((finGL E N).comp (locGL E N w))
    (fun g => (congrArg (finGL E N) (cornerGL_transInv (sLoc E w) g)).trans (cornerGL_transInv (sFin E) _)) g

end GlobalTheory.DiscreteUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitarisStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : LocIrr w N), IsLocCompGL V w σ → IsUnitarisable σ.ρ := by
  first | exact @GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL | exact GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL | (intros; apply GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeNZOfNonVanGen
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DownLift

theorem typeNZ_of_nonVan_gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t → GenInf R i t → GenFin R i t → GoodNoChi R i t → GoodMem R i t → TypeNZ R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i t hNV hInf hFin hNo hMem h hh s hs y hy hg h0
  by_contra hne
  have hF : R.thF i t y = 0 := by
    rw [← hMem y hg, h0]
    exact map_zero _
  exact hFin y (hNo y hg) (hInf y hF) (hNV h hh s hs y hy hne)

end GlobalTheory.DownLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasStringOfLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.LiftInjProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hasString_of_lift (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ok : Pl D.host.E → Prop)
    (h1 : UnrCorr R i t fun w => ¬ ok w) (h1' : UnrCorr R i t ok)
    (h2 : ParamsEx R i t) (h3 : DownEig R i t) {h} (hh : GlobalTheory.Hk3.IsOpsV R i t h) {s : Sys D} {y} (hy : IsEigV R i t h s y)
    (h0 : R.thF i t y ≠ 0) : HasString R i t s := by
  obtain ⟨c, hc⟩ := h3 h hh s
  obtain ⟨B, hB⟩ := h2.1 h hh s y hy (fun e => h0 (by rw [e, map_zero]))
  obtain ⟨B', hB', hb⟩ := h2.2 c ((Submodule.ne_bot_iff _).2 ⟨_, hc y hy, h0⟩)
  refine ⟨B, hB, fun w hw => ⟨(B' w).map (fun a : ℂˣ => ((a * valV R i t w * (valW R i t w)⁻¹ : ℂˣ) : ℂ)), ?_, fun a ha => ?_⟩⟩
  · by_cases hw' : ok w
    · exact h1' h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
    · exact h1 h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
  obtain ⟨b, hb', rfl⟩ := Multiset.mem_map.1 ha
  have e1 : ‖(valV R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  have e2 : ‖(valW R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  simpa [e1, e2] using hb w hw b hb'

theorem liftInj_of_typeNZ : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → (∀ i, TypeNZ R i A.μ0 ∧ DownEig R i A.μ0 ∧ UnrCorr R i A.μ0 (fun w => ¬ Formalism.IndefR.Lev.IsConjPl w w) ∧ UnrCorr R i A.μ0 (fun w => Formalism.IndefR.Lev.IsConjPl w w) ∧ ParamsEx R i A.μ0) → GlobalTheory.LiftRows.LiftInj R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ hZ
  intro i h hops s x y hx hy hxne hyG hy0
  obtain ⟨hT, hDE, hU1, hU2, hPE⟩ := hZ i
  have hF : R.thF i A.μ0 x ≠ 0 := by
    intro h0
    apply hxne
    apply (hG.core.models.HW i (sg0 D A)).1
    rw [hG.core.thP.thG i A.μ0 x, h0, map_zero, map_zero]
  exact hT h hops s (hasString_of_lift R i A.μ0 (fun w => Formalism.IndefR.Lev.IsConjPl w w) hU1 hU2 hPE hDE hops hx hF) y hy hyG hy0

end GlobalTheory.LiftInjProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Gen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ), FinLike R i t f ∧ φ = R.ωP i t (1, g) f}

def TypeVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t),
    R.ωP i t (κ, 1) f = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f

def TypeDiff (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∃ f : WO (Vc D i) (Wc D i) → ℂ,
    IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ φ = R.ωP i t (κ, 1) f - (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f}

def IsLifts (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (κ : G → GA D (Vc D i)) : Prop :=
  ∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g)

def avgW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool) (ε : ℤ)
    (κ : G → GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) : WO (Vc D i) (Wc D i) → ℂ :=
  ∑ g, (mirC R i PP a tr ε g * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • R.ωP i t ((κ g)⁻¹, 1) f

def AvgIm (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 ∧ ∃ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
    ∃ κ : G → GA D (Vc D i), IsLifts R i t κ ∧ ∃ f : WO (Vc D i) (Wc D i) → ℂ,
      IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ φ = avgW R i t PP a tr ε κ f}

def Clean (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ κ : G → GA D (Vc D i), IsLifts R i t κ → avgW R i t PP a tr ε κ f = 0

section ThetaAlg

variable {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D}

theorem heisO_add' (u : WO S T') (f g : WO S T' → ℂ) : heisO ψ S T' u (f + g) = heisO ψ S T' u f + heisO ψ S T' u g := by
  funext w; simp only [heisO, Pi.add_apply]; ring

theorem theta_add {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    IsThetaFunO ψ S T' (f + g) := {
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    rw [heisO_add', hU u hu.1 hi, hU' u hu.2 hi]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem theta_smul (c : ℂ) {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) : IsThetaFunO ψ S T' (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T' u (c • f) = c • heisO ψ S T' u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w) }

theorem theta_sub {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    IsThetaFunO ψ S T' (f - g) := by
  have e : f - g = f + (-1 : ℂ) • g := by funext w; simp [sub_eq_add_neg]
  rw [e]
  exact theta_add hf (theta_smul (-1) hg)

theorem theta_sum {ι : Type} (s : Finset ι) (u : ι → WO S T' → ℂ)
    (f₀ : WO S T' → ℂ) (h₀ : IsThetaFunO ψ S T' f₀) (hu : ∀ k ∈ s, IsThetaFunO ψ S T' (u k)) :
    IsThetaFunO ψ S T' (∑ k ∈ s, u k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := theta_smul (0 : ℂ) h₀
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact theta_add (hu a (Finset.mem_insert_self _ _)) (ih fun k hk => hu k (Finset.mem_insert_of_mem hk))

end ThetaAlg

end GlobalTheory.DownLift.GenFinite

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMulti
noncomputable section

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published

namespace GlobalTheory.LocGL

theorem hasSupport_msupp_of_isL (hZ : ZelevinskyPolynomialRing) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k))
    (h : IsL 𝔪 x.rep) : HasSupport x.rep (msupp 𝔪) := by

  obtain ⟨_, Ψ, -, hΨ, -⟩ := hZ k

  obtain ⟨c, y, hd, ⟨Δ, ⟨hΔ, -⟩, hy⟩, hx⟩ := h

  have key : HasSupport x.rep (∑ a, (Δ a).ms) :=
    SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ (fun a => (hy a).hasSupport) hx.1 hx.isSubquotient

  have e : msupp 𝔪 = ∑ a, (Δ a).ms := by
    rw [← hΔ, msupp, Multiset.bind, Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  rw [e]
  exact key

end GlobalTheory.LocGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorBaseChangeForms
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSS

variable {D : D7} (S : RatDat D.ntw)

def opK (j : ℕ) (f : Module.End D.what₂.LL (S.WL j)) (hf : ∀ x ∈ (S.A j).WK, f x ∈ (S.A j).WK) :
    Module.End S.Ks (FmK S j) :=
  (f.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hf

def goodProjectorBaseChangeForms (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0) :
    Module.End ↥D.LL0 (↥D.LL0 ⊗[S.Ks] FmK S j) :=
  ∑ᶠ g : G0g D.nd, (eC g * (chiL S j hχ (S.eG.symm g))⁻¹) •
    LinearMap.baseChange ↥D.LL0 (rhoKG S j hst (S.eG.symm g))

end GlobalTheory.GoodSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitution
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitution
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatSubst

theorem om_rat_left_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ x, ω (γ, 1) f x = f (actO S T γ⁻¹ 1 x) := by
  intro D ψ S T χS χT ω hω f hf γ hγ x
  have h := GlobalTheory.SiegelFormula.om_rat_apply hω hγ (one_mem (GQ T)) (actO S T γ⁻¹ 1 x) hf
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hω.std hf _)
  have e : actO S T γ 1 (actO S T γ⁻¹ 1 x) = x := by
    have h1 : Formalism.L2.Theta.mt T 1 = 1 := rfl
    have h2 : Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ = 1 := by
      have : Formalism.L2.Theta.mt S (γ * γ⁻¹) = Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ := rfl
      rw [← this, mul_inv_cancel]; rfl
    unfold actO
    rw [inv_inv, h1, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  rwa [e] at h

end GlobalTheory.RatSubst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitutionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_source_acts_on_orientedTheta_by_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ x, ω (γ, 1) f x = f (actO S T γ⁻¹ 1 x) := by
  first | exact @GlobalTheory.RatSubst.om_rat_left_apply | exact GlobalTheory.RatSubst.om_rat_left_apply | (intros; apply GlobalTheory.RatSubst.om_rat_left_apply <;> assumption)
end
end
