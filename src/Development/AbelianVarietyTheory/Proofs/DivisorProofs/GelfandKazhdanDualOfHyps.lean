module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItself
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexConjugateCuspidalRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOfConjPointwise
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory

theorem isCuspForm_of_conj_pointwise : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a), (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) → (∀ o φ, act o (C φ) = C (act o φ)) → (∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ)) → ∀ φ : Sm E a, IsCuspForm φ → IsCuspForm (C φ) := by
  intro E _ _ _ a C hC hact hZ φ hφ
  obtain ⟨h, hc⟩ := hφ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    rw [hC, hC, h.left]
  · convert h.level using 1
    ext k
    change act (.fin k) (C φ) = C φ ↔ act (.fin k) φ = φ
    rw [hact]
    exact C.injective.eq_iff
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hact (.cpt k) φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := hZ z hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  · intro g
    obtain ⟨K, N, h1⟩ := h.growth g
    refine ⟨K, N, fun y => ?_⟩
    rw [hC, RCLike.norm_conj]
    exact h1 y
  · intro r hr0 hra _ _ μ 𝓕 hμ h𝓕 g
    have := hc r hr0 hra μ 𝓕 hμ h𝓕 g
    simp_rw [hC]
    rw [integral_conj, this, map_zero]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAdelicGLComplexConjCommutesOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAdelicGLComplexConjCommutesOperators
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section
namespace GlobalTheory.SmoothConj
open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_conj (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (φ x)) g = Complex.conjCLE ∘ chart φ g := by
  funext x
  simp only [chart, Function.comp_apply]
  split_ifs <;> simp

theorem conj_mem (φ : Sm E a) : (fun x => starRingEnd ℂ (φ.1 x)) ∈ Sm E a := by
  have hφ : ∀ g, ContDiffOn ℝ (↑(⊤ : ℕ∞)) (chart φ.1 g) (invSet E a) := φ.2
  show ∀ g, ContDiffOn ℝ _ (chart (fun x => starRingEnd ℂ (φ.1 x)) g) (invSet E a)
  intro g
  rw [chart_conj]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (hφ g)

def conjMap (φ : Sm E a) : Sm E a := ⟨fun x => starRingEnd ℂ (φ.1 x), conj_mem φ⟩

def conjEquiv : Sm E a ≃ₗ⋆[ℂ] Sm E a where
  toFun := conjMap
  invFun := conjMap
  map_add' x y := by apply Subtype.ext; funext g; simp [conjMap]
  map_smul' c x := by apply Subtype.ext; funext g; simp [conjMap]
  left_inv x := by apply Subtype.ext; funext g; simp [conjMap]
  right_inv x := by apply Subtype.ext; funext g; simp [conjMap]

theorem conjEquiv_act (o : Op E a) (φ : Sm E a) :
    act o (conjEquiv φ) = conjEquiv (act o φ) := by
  cases o with
  | fin k => rfl
  | cpt k => rfl
  | lie X =>
    apply Subtype.ext; funext g
    show lieD X (fun x => starRingEnd ℂ (φ.1 x)) g = starRingEnd ℂ (lieD X φ.1 g)
    simp only [lieD, chart_conj, ContinuousLinearEquiv.comp_fderiv]
    rfl

end GlobalTheory.SmoothConj

namespace GlobalTheory
open GlobalTheory.CuspRep

theorem smooth_conj_commutes_act : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∃ C : Sm E a ≃ₗ⋆[ℂ] Sm E a, (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) ∧
      ∀ o φ, act o (C φ) = C (act o φ) :=
  fun _ _ _ _ _ => ⟨SmoothConj.conjEquiv, fun _ _ => rfl, SmoothConj.conjEquiv_act⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAdelicGLComplexConjCommutesOperatorsStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_adelic_GL_complex_conj_commutes_operators : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ C : Sm E a ≃ₗ⋆[ℂ] Sm E a, (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) ∧ ∀ o φ, act o (C φ) = C (act o φ) := by
  first | exact @GlobalTheory.smooth_conj_commutes_act | exact GlobalTheory.smooth_conj_commutes_act | (intros; apply GlobalTheory.smooth_conj_commutes_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexConjugateCuspidalRepresentation
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory

def CuspRep.CuspSub.mapConj {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (π : CuspSub E a) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hact : ∀ o φ, act o (C φ) = C (act o φ))
    (hcusp : ∀ φ : Sm E a, IsCuspForm φ → IsCuspForm (C φ)) : CuspSub E a where
  V := π.V.map C.toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact hcusp φ (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable o φ hφ, (hact o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := C)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap C.toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← C.injective h2]) fun o φ hφ => by
      change C (act o φ) ∈ W
      rw [← hact]
      exact hs o _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := C.toLinearMap) C.surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem exists_conj_cuspSub : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a),
    ∃ (π' : CuspSub E a) (J : π.V ≃ₗ⋆[ℂ] π'.V), ∀ o φ, J (π.op o φ) = π'.op o (J φ) := by
  intro E _ _ _ a π
  obtain ⟨C, hC, hact⟩ := GlobalTheory.T.smooth_adelic_GL_complex_conj_commutes_operators E a
  have hZ := GlobalTheory.T.capelli_operator_algebra_stable_under_complex_conj E a C hact
  have hcusp := isCuspForm_of_conj_pointwise E a C hC hact hZ
  refine ⟨π.mapConj C hact hcusp, C.submoduleMap π.V, fun o φ => Subtype.ext ?_⟩
  exact (hact o φ.1).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexConjugateCuspidalRepresentationStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_conjugate_cuspidal_representation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∃ (π' : CuspSub E a) (J : π.V ≃ₗ⋆[ℂ] π'.V), ∀ o φ, J (π.op o φ) = π'.op o (J φ) := by
  first | exact @GlobalTheory.exists_conj_cuspSub | exact GlobalTheory.exists_conj_cuspSub | (intros; apply GlobalTheory.exists_conj_cuspSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParameterGLOfConjLinearIntertwiner
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParameterGLOfConjLinearIntertwiner
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.LFun.SatConj

open ComplexConjugate

theorem esymm_map_conj (s : Multiset ℂ) (j : ℕ) : (s.map (starRingEnd ℂ)).esymm j = conj (s.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun t _ => ?_
  simp [map_multiset_prod]

theorem conj_satEig (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    conj (GlobalTheory.LFun.satEig q n B j) = GlobalTheory.LFun.satEig q n (B.map star) j := by
  have hz : conj (((j : ℂ) * ((n : ℂ) - j)) / 2) = ((j : ℂ) * ((n : ℂ) - j)) / 2 := by
    rw [map_div₀, map_mul, map_sub, Complex.conj_natCast, Complex.conj_natCast, map_ofNat]
  have harg : (q : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_pos.ne
  have hp : conj ((q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
    have := Complex.conj_cpow (q : ℂ) (((j : ℂ) * ((n : ℂ) - j)) / 2) harg
    rw [hz, Complex.conj_natCast] at this
    exact this.symm
  have hm : ((B.map star).map fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map (starRingEnd ℂ) := by
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [Units.coe_star]
  rw [GlobalTheory.LFun.satEig, GlobalTheory.LFun.satEig, map_mul, hp, hm, esymm_map_conj]

theorem conj_Tj {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ) (g : GL (Fin n) L) :
    conj (Formalism.UG.Tj ℂ n O ϖ j g) = Formalism.UG.Tj ℂ n O ϖ j g := by
  classical
  unfold Formalism.UG.Tj
  rw [Set.indicator_apply]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
  {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}

theorem isSatVecGL_conj (J : V ≃ₗ⋆[ℂ] W) (hJ : ∀ g x, ρ' g (J x) = J (ρ g x)) {x : V} {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.IsSatVecGL w ρ x B) : GlobalTheory.LFun.IsSatVecGL w ρ' (J x) (B.map star) := by
  obtain ⟨h0, hfix, hcard, hT⟩ := h
  refine ⟨fun e => h0 (J.map_eq_zero_iff.1 e), GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [hJ, GlobalTheory.LGrp.mem_fixed.1 hfix k hk], by simp [hcard], fun ϖ hϖ j hj => ?_⟩
  have hfin := GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x
  have e1 : GlobalTheory.LFun.heckeVec ρ' (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) (J x) =
      J (GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) x) := by
    rw [GlobalTheory.LFun.heckeVec, GlobalTheory.LFun.heckeVec]
    refine (finsum_congr fun c => ?_).trans
      (AddMonoidHom.map_finsum (J.toLinearMap.toAddMonoidHom) hfin).symm
    simp [hJ, conj_Tj]
  rw [e1, hT ϖ hϖ j hj, LinearEquiv.map_smulₛₗ, conj_satEig]

end GlobalTheory.LFun.SatConj


open GlobalTheory.LFun.SatConj in
theorem GlobalTheory.LFun.hasSatGL_of_conjIntertwiner : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (J : V ≃ₗ⋆[ℂ] W), (∀ g x, ρ' g (J x) = J (ρ g x)) → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → GlobalTheory.LFun.HasSatGL w ρ' (B.map star) := by
  intro E _ _ w n V W _ _ _ _ ρ ρ' J hJ B hB
  have hJs : ∀ g y, ρ g (J.symm y) = J.symm (ρ' g y) := fun g y => by
    apply J.injective
    rw [← hJ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := hB.exists_vec
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨J x, (isSatVecGL_conj J hJ hx).2.1, (isSatVecGL_conj J hJ hx).1⟩,
    fun y hy h0 => ?_⟩
  have hy' : J.symm y ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [hJs, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
  have := isSatVecGL_conj J hJ (hB.2 _ hy' fun e => h0 (by simpa using congrArg J e))
  rwa [LinearEquiv.apply_symm_apply] at this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParameterGLOfConjLinearIntertwinerStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_parameter_GL_of_conj_linear_intertwiner : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (J : V ≃ₗ⋆[ℂ] W), (∀ g x, ρ' g (J x) = J (ρ g x)) → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → GlobalTheory.LFun.HasSatGL w ρ' (B.map star) := by
  first | exact @GlobalTheory.LFun.hasSatGL_of_conjIntertwiner | exact GlobalTheory.LFun.hasSatGL_of_conjIntertwiner | (intros; apply GlobalTheory.LFun.hasSatGL_of_conjIntertwiner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCuspidalSatakeParameterStarEqInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCuspidalSatakeParameterStarEqInv
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.UnitaryParam

theorem map_star_eq_map_inv_of_form : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  intro E _ _ _ a π H hH hpos hinv w B hB
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
  refine GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w a π.V (π.locRep w) x B ?_ hx
  refine ⟨H.flip, fun v u => ?_, fun v hv => ?_, fun g v u => ?_⟩
  · simp only [LinearMap.flip_apply]
    exact (hH u v).symm
  · simpa only [LinearMap.flip_apply] using hpos v hv
  · simp only [LinearMap.flip_apply]
    exact hinv _ u v

end GlobalTheory.CuspRep.UnitaryParam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCuspidalSatakeParameterStarEqInvStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_cuspidal_satake_parameter_star_eq_inv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | exact GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | (intros; apply GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItself
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.GKPair

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_inv_map_star {B : Multiset ℂˣ} (h : B.map star = B.map (·⁻¹)) : (B.map (·⁻¹)).map star = B := by
  have e : (B.map (·⁻¹)).map star = (B.map star).map (·⁻¹) := by
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun u _ => ?_
    exact Units.ext (by simp)
  rw [e, h, Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id B]
  exact Multiset.map_congr rfl fun u _ => inv_inv u

theorem paired_of_form (π : CuspSub E a) (L : π.V ≃ₗ⋆[ℂ] π.V)
    (hL : ∀ o ψ, L (π.op (invTOp o) ψ) = π.op o (L ψ)) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ)
    (hpos : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hfin : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ)
    (hcpt : ∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ)
    (hlie : ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0) :
    Paired π π invTOp := by
  let B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ := (H.comp L.toLinearMap).flip
  have hB : ∀ φ ψ, B φ ψ = H (L ψ) φ := fun _ _ => rfl
  have h0 : ∀ φ, H φ φ = 0 → φ = 0 := fun φ h => by
    by_contra hφ
    have := hpos φ hφ
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨B, fun φ h => h0 φ ?_, fun ψ h => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · have := h (L.symm φ)
    rwa [hB, LinearEquiv.apply_symm_apply] at this
  · have := h (L ψ)
    rw [hB] at this
    exact (map_eq_zero_iff L L.injective).1 (h0 _ this)
  · rw [hB, hB, hL, hfin]
  · rw [hB, hB, hL, hcpt]
  · rw [hB, hB, hL, add_comm]
    exact hlie X (L ψ) φ

theorem paired_invTOp (hJS : GlobalTheory.Published.JacquetShalikaRigidity) (hB : GlobalTheory.Published.CuspFormsBoundedGL)
    (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ha : 1 ≤ a) (π : CuspSub E a) (hπ : GlobalTheory.DiscSpec.IsNormalised π) : Paired π π invTOp := by
  obtain ⟨H, hH, hpos, hfin, hcpt, hlie⟩ := GlobalTheory.T.exists_invariant_hermitianForm_cuspidalRep hB E a π hπ
  obtain ⟨π₂, J, hJ⟩ := GlobalTheory.T.exists_complex_conjugate_cuspidal_representation E a (UpperTheory.V.TC.dual π)
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π₂).HasSat w B ∧ (CG.mk π).HasSat w B := by
    refine (GlobalTheory.T.cuspidal_GL_local_components_eventually_satake hA E a π).mono fun w ⟨B, hBw⟩ => ⟨B, ?_, hBw⟩
    have h1 := UpperTheory.V.TC.hasSatGL_dual hBw
    have h2 := GlobalTheory.T.satake_parameter_GL_of_conj_linear_intertwiner E w a _ _ ((UpperTheory.V.TC.dual π).locRep w) (π₂.locRep w) J
      (fun g x => by rw [CuspSub.locRep_eq, CuspSub.locRep_eq, hJ]) _ h1
    have h3 := GlobalTheory.T.unitary_cuspidal_satake_parameter_star_eq_inv E a π H hH hpos hfin w B hBw
    rw [map_inv_map_star h3] at h2
    exact h2
  have e := hJS.strong_multiplicity_one ha (CG.mk π₂) (CG.mk π) hsat
  obtain ⟨T, hT⟩ : CuspSub.Iso π₂ π := Quotient.exact e
  let L : π.V ≃ₗ⋆[ℂ] π.V := ((UpperTheory.V.TC.toDual π).trans J).trans T
  refine paired_of_form π L (fun o ψ => ?_) H hpos hfin hcpt hlie
  change T (J (UpperTheory.V.TC.toDual π (π.op (invTOp o) ψ))) = π.op o (T (J (UpperTheory.V.TC.toDual π ψ)))
  rw [← UpperTheory.V.TC.op_toDual, hJ, hT]

end GlobalTheory.GKPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItselfStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_rep_paired_with_itself : GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.CuspFormsBoundedGL → GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, GlobalTheory.DiscSpec.IsNormalised π → Paired π π invTOp := by
  first | exact @GlobalTheory.GKPair.paired_invTOp | exact GlobalTheory.GKPair.paired_invTOp | (intros; apply GlobalTheory.GKPair.paired_invTOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistCuspidalTrivialOnSplitCentre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistCuspidalTrivialOnSplitCentre
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GKNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_splitCentre_eigen (π : CuspSub E a) : ∃ c : ℂ, ∀ φ ∈ π.V, ∀ (t : ℝ) (g : GA E a),
    φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  obtain ⟨c, hc⟩ := GlobalTheory.CuspRep.Central.lie_scalar π (1 : Cinf E)
  refine ⟨c, fun φ hφ t g => ?_⟩
  have e3 : GlobalTheory.CuspRep.Central.scL a (fun _ : InfinitePlace E => (t : ℂ)) =
      t • GlobalTheory.CuspRep.Central.scL (E := E) a 1 := by
    ext i j w
    by_cases hij : i = j <;> simp [hij]
  have h1 := GlobalTheory.CuspRep.Central.rs_exp (fun _ : InfinitePlace E => (t : ℂ)) (c * t) φ (by
    rw [e3, map_smul, LinearMap.smul_apply, hc φ hφ, mul_comm, mul_smul, Complex.coe_smul])
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar]
  exact congrFun (congrArg Subtype.val h1) g

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, ∃ χ : HChar E, GlobalTheory.DiscSpec.IsNormalised (π.twist χ) := by
  intro E _ _ _ a ha π
  obtain ⟨c, hs⟩ := exists_splitCentre_eigen π
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) (a := a) (by omega) (-c)
  refine ⟨χ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩ t g
  change (mulChi a χ φ).1 _ = (mulChi a χ φ).1 _
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hχ, hs φ hφ, mul_mul_mul_comm, ← Complex.exp_add]
  simp

end GlobalTheory.GKNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistCuspidalTrivialOnSplitCentreStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twist_cuspidal_trivial_on_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, ∃ χ : HChar E, GlobalTheory.DiscSpec.IsNormalised (π.twist χ) := by
  first | exact @GlobalTheory.GKNorm.exists_twist_isNormalised | exact GlobalTheory.GKNorm.exists_twist_isNormalised | (intros; apply GlobalTheory.GKNorm.exists_twist_isNormalised <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

theorem gelfandKazhdanDual_of_rapidDecay : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.CuspRapidDecaySiegelGL → GlobalTheory.Published.GelfandKazhdanDual := by
  intro hJS hAF hRD E _ _ _ n π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.Published.InvTransposeModel.rank_zero π
  · obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_twist_cuspidal_trivial_on_splitCentre E n hn π
    have hp := GlobalTheory.T.cusp_rep_paired_with_itself hJS.1 (GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay hRD) hAF E n hn (π.twist χ) hχ
    have h := GlobalTheory.Published.InvTransposeModel.twist hp χ⁻¹
    rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GelfandKazhdanTop
