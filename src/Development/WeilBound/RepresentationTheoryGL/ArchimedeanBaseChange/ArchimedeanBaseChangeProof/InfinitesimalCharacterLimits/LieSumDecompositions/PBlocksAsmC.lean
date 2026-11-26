module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapE
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.InfTree
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfIsAutFormTotallyComplex
open NumberField

namespace GlobalTheory.CompanionTheory.ContAutForm

open GlobalTheory.CuspRep

theorem continuous_of_isAutForm_totallyComplex (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)
    (φ : Sm E N) (h : IsAutForm φ) : Continuous φ.1 :=
  h.continuous

end GlobalTheory.CompanionTheory.ContAutForm
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmB
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmA
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

theorem factor {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (U : Submodule ℂ M)
    (T : M →ₗ[ℂ] N) (T' : M →ₗ[ℂ] N) (h : ∀ ψ ∈ U, T ψ = 0 → T' ψ = 0) :
    ∃ P : N →ₗ[ℂ] N, ∀ ψ ∈ U, P (T ψ) = T' ψ := by
  let f := T ∘ₗ U.subtype
  let g := T' ∘ₗ U.subtype
  have hle : LinearMap.ker f ≤ LinearMap.ker g := fun x hx => h x.1 x.2 hx
  let g₀ := (LinearMap.ker f).liftQ g hle
  let h₀ : LinearMap.range f →ₗ[ℂ] N := g₀ ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨P, hP⟩ := LinearMap.exists_extend h₀
  refine ⟨P, fun ψ hψ => ?_⟩
  have e1 : P (T ψ) = h₀ ⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩ :=
    LinearMap.congr_fun hP (⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩ : LinearMap.range f)
  rw [e1]
  change g₀ (f.quotKerEquivRange.symm ⟨f ⟨ψ, hψ⟩, _⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem eq_of_levi {F₁ F₂ : Sm E (r + s)}
    (h₁ : ∀ (x : BlockIx (r + s) r → Ad E) g, F₁.1 (unip x * g) = F₁.1 g)
    (h₂ : ∀ (x : BlockIx (r + s) r → Ad E) g, F₂.1 (unip x * g) = F₂.1 g)
    (h : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F₁.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        F₂.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) : F₁ = F₂ := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨u, m, k, g, rfl⟩ := ParabolicProjection.exists_decomp x
  rw [mul_assoc, h₁, h₂]
  exact h k g m

theorem eq_zero_of_levi {F : Sm E (r + s)} (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (h : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) = 0) : F = 0 :=
  eq_of_levi hF (fun _ _ => rfl) h

theorem isStable_map {a : ℕ} {L : Submodule ℂ (Sm E a)} (hL : _root_.GlobalTheory.CuspRep.IsStable L) {z : Module.End ℂ (Sm E a)}
    (hz : ∀ o : Op E a, Commute z (act o)) : _root_.GlobalTheory.CuspRep.IsStable (L.map z) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨act o φ, hL o φ hφ, by
    change z (act o φ) = act o (z φ)
    rw [← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]⟩

theorem finGen_map {a : ℕ} {L : Submodule ℂ (Sm E a)} {z : Module.End ℂ (Sm E a)}
    (hz : ∀ o : Op E a, Commute z (act o)) (S₁ : Finset (Sm E a)) (hS₁ : (↑S₁ : Set (Sm E a)) ⊆ L)
    (hgen : ∀ W : Submodule ℂ (Sm E a), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E a)) ⊆ W → L ≤ W) : FinGen (L.map z) := by
  classical
  refine ⟨S₁.image z, fun x hx => ?_, fun W hW hSW => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact Submodule.mem_map_of_mem (hS₁ hy)
  · have hst : _root_.GlobalTheory.CuspRep.IsStable (W.comap z) := fun o φ hφ => by
      change z (act o φ) ∈ W
      rw [← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]
      exact hW o _ hφ
    have hle := hgen (W.comap z) hst fun y hy => hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem z hy))
    rintro _ ⟨φ, hφ, rfl⟩
    exact hle hφ

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksTwHyp
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open scoped Classical

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem mulChi_neg_cancel (w : ℂ) (ψ : Sm E a) :
    mulChi a (Model.absC E (-w)) (mulChi a (Model.absC E w) ψ) = ψ := by
  have h := ChordArithmetic.mulChi_absC_cancel (E := E) a (-w) ψ
  rwa [neg_neg] at h

theorem isAutSt_tw {V : Submodule ℂ (Sm E a)} (hV : IsAutSt V) (w : ℂ) : IsAutSt (tw V w) := by
  refine ⟨ParabolicProjection.isStable_tw hV.1 w, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  have h := hV.2 ψ hψ
  let χ := Model.absC E w
  change IsAutForm (mulChi a χ ψ)
  exact {
      left γ g := by simp [h.left, chiDet_ratGL]
      level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : GlobalTheory.CuspRep.rt E a (finGL E a k) ψ = ψ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change GlobalTheory.CuspRep.rt E a (finGL E a k) _ = _
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
      kfin := by
        have := h.kfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)).map
          (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ ψ).symm⟩
      zfin := by
        have := h.zfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) ''
          Zalg E a)).map (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
        exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 ψ).symm⟩
      growth g := by
        obtain ⟨C, N, h1⟩ := h.growth g
        obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
        refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
        rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
        refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
          ((norm_nonneg _).trans (h1 y))).trans_eq ?_
        ring
  }

theorem finGen_tw {V : Submodule ℂ (Sm E a)} (hV : FinGen V) (w : ℂ) : FinGen (tw V w) := by
  obtain ⟨S, hS, hgen⟩ := hV
  refine ⟨S.image (mulChi a (Model.absC E w)), ?_, fun W hW hSW => ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact Submodule.mem_map_of_mem (hS (Finset.mem_coe.2 hy))
  · have hle : V ≤ tw W (-w) := hgen _ (ParabolicProjection.isStable_tw hW (-w)) (fun y hy => by
      have hmem : mulChi a (Model.absC E w) y ∈ W :=
        hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hy)))
      have h : (mulChi a (Model.absC E (-w))).toLinearMap (mulChi a (Model.absC E w) y) ∈ tw W (-w) :=
        Submodule.mem_map_of_mem hmem
      rw [LinearEquiv.coe_coe, mulChi_neg_cancel] at h
      exact h)
    intro φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
    obtain ⟨χ, hχ, rfl⟩ := Submodule.mem_map.1 (hle hψ)
    have e := ChordArithmetic.mulChi_absC_cancel (E := E) a w χ
    simp only [LinearEquiv.coe_coe] at e ⊢
    rw [e]
    exact hχ

theorem infNodup_tw {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} (h : ∃ m, HasInfCharGL V τ m ∧ m.Nodup) (w : ℂ) :
    ∃ m, HasInfCharGL (tw V w) τ m ∧ m.Nodup := by
  obtain ⟨m, hm, hnd⟩ := h
  exact ⟨m.map (· + w), SpectralAccumulation.Trees.hasInfCharGL_tw hm w, hnd.map (add_left_injective w)⟩

theorem regAll_tw {V : Submodule ℂ (Sm E a)} (hV : RegAll V) (w : ℂ) : RegAll (tw V w) :=
  fun τ => infNodup_tw (hV τ) w

theorem hyp_tw {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} (w : ℂ) (hA : IsAutSt V) (hF : FinGen V)
    (hI : ∃ m, HasInfCharGL V τ m ∧ m.Nodup) (hR : RegAll V) (hN : SpectralAccumulation.NonPos (tw V w)) (hC : SpectralAccumulation.CentIm (tw V w)) :
    Hyp τ (tw V w) :=
  ⟨isAutSt_tw hA w, finGen_tw hF w, hN, hC, infNodup_tw hI w, regAll_tw hR w⟩

theorem tw_tw_neg (V : Submodule ℂ (Sm E a)) (w : ℂ) : tw (tw V (-w)) w = V := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨χ, hχ, rfl⟩ := Submodule.mem_map.1 hφ
    obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hχ
    simp only [LinearEquiv.coe_coe]
    rw [ChordArithmetic.mulChi_absC_cancel]
    exact hψ
  · intro hφ
    have h1 : (mulChi a (Model.absC E (-w))).toLinearMap φ ∈ tw V (-w) := Submodule.mem_map_of_mem hφ
    have h2 := Submodule.mem_map_of_mem (f := (mulChi a (Model.absC E w)).toLinearMap) h1
    simp only [LinearEquiv.coe_coe] at h2
    rw [ChordArithmetic.mulChi_absC_cancel] at h2
    exact h2

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksExp
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PExpFin

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

def tl (r : ℕ) (s : ℝ) : Module.End ℂ (GA E N → ℂ) where
  toFun f g := f (aT E N r s * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tl_pow (r : ℕ) (s : ℝ) (i : ℕ) (f : GA E N → ℂ) : (tl r s ^ i) f = fun g => f (aT E N r (s * i) * g) := by
  induction i generalizing f with
  | zero =>
    funext g
    simp [aT_zero]
  | succ i ih =>
    funext g
    rw [pow_succ, Module.End.mul_apply, ih]
    show f (aT E N r s * (aT E N r (s * i) * g)) = f (aT E N r (s * ((i + 1 : ℕ) : ℝ)) * g)
    rw [← mul_assoc, ← aT_add, show s + s * (i : ℝ) = s * ((i + 1 : ℕ) : ℝ) by push_cast; ring]

theorem kl_iff (r : ℕ) (s : ℝ) (p : ℂ[X]) (F : GA E N → ℂ) : Kl r s p F ↔ aeval (tl r s) p F = 0 := by
  have e : aeval (tl (N := N) r s) p F = fun g => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F (aT E N r (s * j) * g) := by
    rw [aeval_eq_sum_range, LinearMap.sum_apply]
    funext g
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, tl_pow]
    rfl
  rw [e]
  constructor
  · intro h
    funext g
    exact h g
  · intro h g
    exact congrFun h g

theorem kl_mul {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) : Kl r s (p * q) F := by
  rw [kl_iff] at h ⊢
  rw [mul_comm, aeval_mul, Module.End.mul_apply, h, map_zero]

theorem kl_mul' {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s q F) : Kl r s (p * q) F := by
  rw [mul_comm]
  exact kl_mul h

theorem ctn_eq_ct (r : ℕ) :
    letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
    ∃ μ : Measure (BlockIx N r → Ad E), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratN E N r) (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) μ ∧
      ∀ f : Sm E N, An.ctn r f.1 = PositivityTheory.Affgl.CT.ct μ (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) f.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  refine ⟨μ, hμ, hD, fun f => funext fun g => ?_⟩
  show An.ctn r f.1 g = ∫ x in GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r, f.1 (unip x * g) ∂μ
  rw [hint]
  simp only [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]

theorem ctn_add (r : ℕ) {φ ψ : Sm E N} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) :
    An.ctn r (φ + ψ).1 = An.ctn r φ.1 + An.ctn r ψ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, e⟩ := ctn_eq_ct (E := E) (N := N) r
  have := hμ
  rw [e, e, e]
  exact ct_add μ _ hD hφ hψ

theorem ctn_smul (r : ℕ) (c : ℂ) (φ : Sm E N) : An.ctn r (c • φ).1 = c • An.ctn r φ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨μ, -, -, e⟩ := ctn_eq_ct (E := E) (N := N) r
  rw [e, e]
  exact ct_smul μ _ c φ

def Good (β : ℕ → ℝ) (φ : Sm E N) : Prop :=
  IsAutForm φ ∧ ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ Kl r 1 p (An.ctn r φ.1) ∧ ∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp (β r)

theorem good_bound {β : ℕ → ℝ} {φ : Sm E N} (h : Good β φ) :
    ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro r hr hrN c hc
  obtain ⟨p, -, hk, hroot⟩ := h.2 r hr hrN
  obtain ⟨F₀, hCT, F, hFspan, hF0, hFe⟩ := hc
  obtain ⟨-, -, -, hD⟩ := dict_holds E N
  obtain ⟨c₁, -, e₁⟩ := (hD φ h.1 r hr hrN).2 F₀ hCT
  have hk₀ : Kl r 1 p F₀ := by
    have : F₀ = c₁ • An.ctn r φ.1 := by
      funext g
      rw [e₁]
      rfl
    rw [this]
    exact (klSub r 1 p).smul_mem c₁ hk
  have hroot' := kl_eigen (kl_span hk₀ hFspan) hF0 hFe
  have h1 := hroot (Complex.exp (c * ((1 : ℝ) : ℂ))) hroot'
  rw [Complex.norm_exp] at h1
  have h2 := Real.exp_le_exp.1 h1
  simpa using h2

theorem good_of (β : ℕ → ℝ) {φ : Sm E N} (hφ : IsAutForm φ)
    (hexp : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) : Good β φ := by
  refine ⟨hφ, fun r hr hrN => ?_⟩
  obtain ⟨hA, -, -, hCT⟩ := dict_holds E N
  have hct := (hCT φ hφ r hr hrN).1
  have hfin := finTr_holds E N φ hφ r hr hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => aT_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp (GlobalTheory.CompanionTheory.ContAutForm.continuous_of_isAutForm_totallyComplex E N φ hφ) r
      ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [one_mul] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    have hc : c ∈ Exp r φ.1 := ⟨_, hct, F, hF, hF0, hFe⟩
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (hexp r hr hrN c hc)

theorem good_add {β : ℕ → ℝ} {φ ψ : Sm E N} (hφ : Good β φ) (hψ : Good β ψ) : Good β (φ + ψ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hφ.1 hψ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  obtain ⟨q, hq, hqk, hqr⟩ := hψ.2 r hr hrN
  refine ⟨p * q, hp.mul hq, ?_, fun z hz => ?_⟩
  · rw [ctn_add r hφ.1 hψ.1]
    exact (klSub r 1 (p * q)).add_mem (kl_mul hpk) (kl_mul' hqk)
  · rcases (Polynomial.root_mul.1 hz) with h | h
    · exact hpr z h
    · exact hqr z h

theorem good_smul {β : ℕ → ℝ} {φ : Sm E N} (hφ : Good β φ) (c : ℂ) : Good β (c • φ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul c hφ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  refine ⟨p, hp, ?_, hpr⟩
  rw [ctn_smul]
  exact (klSub r 1 p).smul_mem c hpk

theorem good_zero (β : ℕ → ℝ) : Good β (0 : Sm E N) := by
  refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun r hr hrN => ⟨1, monic_one, ?_, fun z hz => ?_⟩⟩
  · have e : An.ctn r (0 : Sm E N).1 = (0 : ℂ) • An.ctn r (0 : Sm E N).1 := by
      rw [← ctn_smul, zero_smul]
    rw [e]
    exact (klSub r 1 1).smul_mem 0 (by
      intro g
      simp [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm])
  · exact absurd hz (by simp [Polynomial.IsRoot])

theorem exp_span (S : Set (Sm E N)) (β : ℕ → ℝ) (haut : ∀ φ ∈ S, IsAutForm φ)
    (hexp : ∀ φ ∈ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) :
    ∀ φ ∈ Submodule.span ℂ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro φ hφ
  refine good_bound ?_
  induction hφ using Submodule.span_induction with
  | mem x hx => exact good_of β (haut x hx) (hexp x hx)
  | zero => exact good_zero β
  | add x y _ _ hx hy => exact good_add hx hy
  | smul c x _ hx => exact good_smul hx c

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksTwNonPos
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem pE_shift (a r : ℕ) (c w : ℂ) :
    pE E a r (c + w * r * (Module.finrank ℚ E : ℂ)) = pE E a r c + w.re * r := by
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact_mod_cast this.ne'
  unfold pE
  have e : (c + w * r * (Module.finrank ℚ E : ℂ)).re = c.re + w.re * r * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re]
  rw [e]
  field_simp
  ring

theorem nonPos_tw {a : ℕ} (V : Submodule ℂ (Sm E a)) (w : ℂ) (haut : ∀ φ ∈ V, IsAutForm φ)
    (hV : ∀ φ ∈ V, ∀ r, 0 < r → r < a → ∀ c ∈ Exp r φ.1, pE E a r c + w.re * r ≤ 0) :
    SpectralAccumulation.NonPos (tw V w) := by
  intro φ hφ r hr hra c hc
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  have h0 := expTw_holds E a ψ w (haut ψ hψ) r hr hra c hc
  have h1 := hV ψ hψ r hr hra _ h0
  have e : c = (c - w * r * (Module.finrank ℚ E : ℂ)) + w * r * (Module.finrank ℚ E : ℂ) := by ring
  rw [e, pE_shift]
  exact h1

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksTwCent
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem central_mulChi {a : ℕ} (e w : ℂ) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) (t : ℝ) (m : GA E a) :
    (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) =
      Complex.exp ((e + w * a * (Module.finrank ℚ E : ℂ)) * t) * (mulChi a (Model.absC E w) ψ).1 m := by
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl,
    add_mul, Complex.exp_add]
  ring

theorem centIm_tw {a : ℕ} (V : Submodule ℂ (Sm E a)) (e w : ℂ) (he : (e + w * a * (Module.finrank ℚ E : ℂ)).re = 0)
    (hV : ∀ φ ∈ V, ∀ (t : ℝ) m, φ.1 (splitCentre E a t * m) = Complex.exp (e * t) * φ.1 m) :
    SpectralAccumulation.CentIm (tw V w) := by
  refine ⟨_, he, fun φ hφ t g => ?_⟩
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  exact central_mulChi e w ψ (hV ψ hψ) t g

omit [IsCMField E] in
theorem finrank_ne_zero' : (Module.finrank ℚ E : ℝ) ≠ 0 := by
  have : 0 < Module.finrank ℚ E := Module.finrank_pos
  exact_mod_cast this.ne'

theorem re_of_pE {r s : ℕ} {c : ℂ} (hc : pE E (r + s) r c = 0) :
    c.re = (r : ℝ) * s * (Module.finrank ℚ E : ℝ) / 2 := by
  have hd := finrank_ne_zero' (E := E)
  unfold pE at hc
  push_cast at hc
  field_simp at hc
  linarith

theorem centIm_left {r s : ℕ} (V : Submodule ℂ (Sm E r)) {c : ℂ} (hc : pE E (r + s) r c = 0)
    (hV : ∀ φ ∈ V, ∀ (t : ℝ) m, φ.1 (splitCentre E r t * m) = Complex.exp (c * t) * φ.1 m) :
    SpectralAccumulation.CentIm (tw V (-(s : ℂ) / 2)) := by
  refine centIm_tw V c _ ?_ hV
  have h := re_of_pE (E := E) hc
  have e1 : (c + -(s : ℂ) / 2 * r * (Module.finrank ℚ E : ℂ)).re = c.re - (s : ℝ) / 2 * r * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re, Complex.neg_re] <;> ring_nf
  rw [e1, h]; ring

theorem centIm_right {r s : ℕ} (V : Submodule ℂ (Sm E s)) {c : ℂ} (hc : pE E (r + s) r c = 0)
    (hV : ∀ φ ∈ V, ∀ (t : ℝ) m, φ.1 (splitCentre E s t * m) = Complex.exp (-c * t) * φ.1 m) :
    SpectralAccumulation.CentIm (tw V ((r : ℂ) / 2)) := by
  refine centIm_tw V (-c) _ ?_ hV
  have h := re_of_pE (E := E) hc
  have e1 : (-c + (r : ℂ) / 2 * s * (Module.finrank ℚ E : ℂ)).re = -c.re + (r : ℝ) / 2 * s * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re, Complex.neg_re] <;> ring_nf
  rw [e1, h]; ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
end

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem d_pos : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by
  have : 0 < Module.finrank ℚ E := Module.finrank_pos
  exact_mod_cast this

theorem LS_exp (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) :
    ∀ φ ∈ LS U T, ∀ r', 0 < r' → r' < r → ∀ c' ∈ Exp r' φ.1,
      c'.re ≤ (Module.finrank ℚ E : ℝ) * ((r' : ℝ) * (((r + s : ℕ) : ℝ) - r')) / 2 := by
  refine BlockExponential.exp_span _ _ (fun φ hφ => BlockSlices.LS_aut hT φ (Submodule.subset_span hφ)) ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₂, hℓ⟩ r' hr' hrr c' hc'
  obtain ⟨ψ₁, -, h1, -, hexp⟩ := hT.left ψ hψ k g m₂
  have e : ℓ = ψ₁ := Subtype.ext (funext fun m₁ => (hℓ m₁).trans (h1 m₁).symm)
  rw [e] at hc'
  obtain ⟨φ, hφ, hcφ⟩ := hexp r' hr' hrr c' hc'
  have h := hNP φ hφ r' hr' (by omega) c' hcφ
  have hd := d_pos (E := E)
  unfold pE at h
  have h2 : c'.re / (Module.finrank ℚ E : ℝ) ≤ (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 := by linarith
  rw [div_le_iff₀ hd] at h2
  have e2 : (Module.finrank ℚ E : ℝ) * ((r' : ℝ) * (((r + s : ℕ) : ℝ) - r')) / 2 =
      (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 * (Module.finrank ℚ E : ℝ) := by ring
  linarith

theorem RS_exp (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) :
    ∀ φ ∈ RS U T, ∀ r₂, 0 < r₂ → r₂ < s → ∀ c₂ ∈ Exp r₂ φ.1,
      c₂.re ≤ (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - c.re := by
  refine BlockExponential.exp_span _ (fun r₂ => (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) *
    (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - c.re) (fun φ hφ => BlockSlices.RS_aut hT φ (Submodule.subset_span hφ)) ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₁, hℓ⟩ r₂ hr₂ hrs c₂ hc₂
  obtain ⟨ψ₂, -, h1, -, hexp⟩ := hT.right ψ hψ k g m₁
  have e : ℓ = ψ₂ := Subtype.ext (funext fun m₂ => (hℓ m₂).trans (h1 m₂).symm)
  rw [e] at hc₂
  obtain ⟨φ, hφ, hcφ⟩ := hexp r₂ hr₂ hrs c₂ hc₂
  have h := hNP φ hφ (r + r₂) (by omega) (by omega) (c + c₂) hcφ
  have hd := d_pos (E := E)
  unfold pE at h
  rw [Complex.add_re] at h
  have h2 : (c.re + c₂.re) / (Module.finrank ℚ E : ℝ) ≤
      ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 := by linarith
  rw [div_le_iff₀ hd] at h2
  have e2 : (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 =
      ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 * (Module.finrank ℚ E : ℝ) := by ring
  linarith

theorem LS_cent (hT : IsSliceMap U c T) :
    ∀ φ ∈ LS U T, ∀ (t : ℝ) m, φ.1 (splitCentre E r t * m) = Complex.exp (c * t) * φ.1 m := by
  intro φ hφ t m
  induction hφ using Submodule.span_induction generalizing m with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ₁, -, h1, hc, -⟩ := hT.left ψ hψ k g m₂
    have e : x = ψ₁ := Subtype.ext (funext fun m₁ => (hx m₁).trans (h1 m₁).symm)
    rw [e]
    exact hc t m
  | zero => simp
  | add x y _ _ hx hy =>
    change x.1 _ + y.1 _ = _ * (x.1 m + y.1 m)
    rw [hx, hy, mul_add]
  | smul a x _ hx =>
    change a * x.1 _ = _ * (a * x.1 m)
    rw [hx]
    ring

theorem RS_cent (hT : IsSliceMap U c T) :
    ∀ φ ∈ RS U T, ∀ (t : ℝ) m, φ.1 (splitCentre E s t * m) = Complex.exp (-c * t) * φ.1 m := by
  intro φ hφ t m
  induction hφ using Submodule.span_induction generalizing m with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ₂, -, h1, hc, -⟩ := hT.right ψ hψ k g m₁
    have e : x = ψ₂ := Subtype.ext (funext fun m₂ => (hx m₂).trans (h1 m₂).symm)
    rw [e]
    exact hc t m
  | zero => simp
  | add x y _ _ hx hy =>
    change x.1 _ + y.1 _ = _ * (x.1 m + y.1 m)
    rw [hx, hy, mul_add]
  | smul a x _ hx =>
    change a * x.1 _ = _ * (a * x.1 m)
    rw [hx]
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
end

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem inf_piece {a : ℕ} {X : Submodule ℂ (Sm E a)} {σ : (E →+* ℂ) → Multiset ℂ} {sh : ℂ}
    (mm : (E →+* ℂ) → Multiset ℂ) (hmmN : ∀ τ, (mm τ).Nodup) (hσ : σ ∈ adm mm a)
    (hX : ∀ φ ∈ X, ∀ τ w, cap τ w φ = ((σ τ).map (fun z => w + sh + z)).prod • φ) (τ : E →+* ℂ) :
    HasInfCharGL X τ ((σ τ).map (· + sh)) ∧ ((σ τ).map (· + sh)).Nodup := by
  refine ⟨⟨by rw [Multiset.card_map]; exact (mem_adm.1 hσ τ).2, fun u φ hφ => ?_⟩,
    (Multiset.nodup_of_le (mem_adm.1 hσ τ).1 (hmmN τ)).map (add_left_injective sh)⟩
  rw [hX φ hφ τ u, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun z _ => by simp only [Function.comp_apply]; ring

theorem hyp_left (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) (hpE : pE E (r + s) r c = 0)
    (mm : (E →+* ℂ) → Multiset ℂ) (hmmN : ∀ τ, (mm τ).Nodup) {σ : (E →+* ℂ) → Multiset ℂ} (hσ : σ ∈ adm mm r)
    {z : Module.End ℂ (Sm E r)} (hzc : ∀ o, Commute z (act o))
    (hzE : ∀ φ ∈ LS U T, z φ ∈ Eig (LS U T) σ ((s : ℂ) / 2))
    (hfg : ∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ LS U T ∧
      ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → LS U T ≤ W) (τ : E →+* ℂ) :
    Hyp τ (tw ((LS U T).map z) (-(s : ℂ) / 2)) := by
  have hXle : (LS U T).map z ≤ LS U T := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).1
  have hXE : ∀ φ ∈ (LS U T).map z, ∀ τ w, cap τ w φ = ((σ τ).map (fun x => w + (s : ℂ) / 2 + x)).prod • φ := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).2
  have hinf := inf_piece mm hmmN hσ hXE
  obtain ⟨S₁, hS₁, hgen⟩ := hfg
  have haut : ∀ φ ∈ (LS U T).map z, IsAutForm φ := fun φ hφ => BlockSlices.LS_aut hT φ (hXle hφ)
  refine BlockTwistCharacters.hyp_tw (-(s : ℂ) / 2) ⟨isStable_map (BlockSlices.LS_stable hU hT) hzc, haut⟩ (finGen_map hzc S₁ hS₁ hgen)
    ⟨_, hinf τ⟩ (fun τ' => ⟨_, hinf τ'⟩) ?_ (BlockTwistCharacters.centIm_left _ hpE fun φ hφ => LS_cent hT φ (hXle hφ))
  refine BlockTwistCharacters.nonPos_tw _ _ haut fun φ hφ r' hr' hrr c' hc' => ?_
  have hb := LS_exp hU hNP hT φ (hXle hφ) r' hr' hrr c' hc'
  have hd := d_pos (E := E)
  have h2 : c'.re / (Module.finrank ℚ E : ℝ) ≤ (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 := by
    rw [div_le_iff₀ hd]
    linarith
  unfold pE
  have e : (-(s : ℂ) / 2).re = -(s : ℝ) / 2 := by simp
  rw [e]
  push_cast at h2 ⊢
  nlinarith

theorem hyp_right (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) (hpE : pE E (r + s) r c = 0)
    (mm : (E →+* ℂ) → Multiset ℂ) (hmmN : ∀ τ, (mm τ).Nodup) {ρ : (E →+* ℂ) → Multiset ℂ} (hρ : ρ ∈ adm mm s)
    {z : Module.End ℂ (Sm E s)} (hzc : ∀ o, Commute z (act o))
    (hzE : ∀ φ ∈ RS U T, z φ ∈ Eig (RS U T) ρ (-(r : ℂ) / 2))
    (hfg : ∃ S₁ : Finset (Sm E s), (↑S₁ : Set (Sm E s)) ⊆ RS U T ∧
      ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E s)) ⊆ W → RS U T ≤ W) (τ : E →+* ℂ) :
    Hyp τ (tw ((RS U T).map z) ((r : ℂ) / 2)) := by
  have hXle : (RS U T).map z ≤ RS U T := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).1
  have hXE : ∀ φ ∈ (RS U T).map z, ∀ τ w, cap τ w φ = ((ρ τ).map (fun x => w + -(r : ℂ) / 2 + x)).prod • φ := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).2
  have hinf := inf_piece mm hmmN hρ hXE
  obtain ⟨S₁, hS₁, hgen⟩ := hfg
  have haut : ∀ φ ∈ (RS U T).map z, IsAutForm φ := fun φ hφ => BlockSlices.RS_aut hT φ (hXle hφ)
  refine BlockTwistCharacters.hyp_tw ((r : ℂ) / 2) ⟨isStable_map (BlockSlices.RS_stable hU hT) hzc, haut⟩ (finGen_map hzc S₁ hS₁ hgen)
    ⟨_, hinf τ⟩ (fun τ' => ⟨_, hinf τ'⟩) ?_ (BlockTwistCharacters.centIm_right _ hpE fun φ hφ => RS_cent hT φ (hXle hφ))
  refine BlockTwistCharacters.nonPos_tw _ _ haut fun φ hφ r₂ hr₂ hrs c₂ hc₂ => ?_
  have hb := RS_exp hU hNP hT φ (hXle hφ) r₂ hr₂ hrs c₂ hc₂
  have hd := d_pos (E := E)
  have hc := BlockTwistCharacters.re_of_pE (E := E) hpE
  have h2 : c₂.re / (Module.finrank ℚ E : ℝ) ≤
      ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 - (r : ℝ) * s / 2 := by
    rw [div_le_iff₀ hd]
    have e3 : (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 - (r : ℝ) * s / 2) *
        (Module.finrank ℚ E : ℝ) = (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) *
        (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - (r : ℝ) * s * (Module.finrank ℚ E : ℝ) / 2 := by ring
    rw [e3, ← hc]
    exact hb
  unfold pE
  have e : ((r : ℂ) / 2).re = (r : ℝ) / 2 := by simp
  rw [e]
  push_cast at h2 ⊢
  nlinarith

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
