module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOne
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SmoothCharDet

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

theorem isSmoothChar_of_detChar_apow_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  intro k _ _ _ _ n hn ν s P hP hν
  let i0 : Fin n := ⟨0, hn⟩
  let d : kˣ →* GL (Fin n) k :=
    (diagHom (k := k) (n := Fin n)).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i0)
  have hval : Continuous fun x : kˣ => ((d x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    show Continuous fun x : kˣ => diagonal fun i => (((Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x) i : kˣ) : k)
    exact Continuous.matrix_diagonal (continuous_pi fun i =>
      Units.continuous_val.comp ((continuous_apply i).comp (continuous_mulSingle (A := fun _ : Fin n => kˣ) i0)))
  have hd : Continuous d := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have := hval.comp continuous_inv
    simpa [Function.comp_def, map_inv] using this
  have hdet : ∀ x : kˣ, gdet (d x) = x := fun x => by
    show Matrix.GeneralLinearGroup.det (diagGL (Pi.mulSingle (M := fun _ : Fin n => kˣ) i0 x)) = x
    rw [det_diagGL]
    simp
  have hU : (d : kˣ → GL (Fin n) k) ⁻¹' (P ∩ (KO k (Fin n) : Set (GL (Fin n) k))) ∈ 𝓝 (1 : kˣ) := by
    refine hd.continuousAt.preimage_mem_nhds ?_
    rw [map_one]
    exact Filter.inter_mem hP (isOpen_KO.mem_nhds (one_mem _))
  refine Subgroup.isOpen_of_mem_nhds ν.ker (Filter.mem_of_superset hU fun x hx => ?_)
  have h1 := hν _ hx.1
  rw [apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.2), mul_one, hdet] at h1
  exact MonoidHom.mem_ker.2 (Units.ext h1)

end GlobalTheory.SmoothCharDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOneStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_character_of_trivial_near_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  first | exact @GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds | exact GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds | (intros; apply GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnity
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.NuGood

theorem not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h v hv t k hk hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl (F := F))) := by
    intro hmem
    exact hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.T.unramified_character_at_uniformizer F E X.ν v t hunr] at hpow
  have hHecke : IsHecke F E X.ν := by
    refine ⟨?_, fun x => ?_⟩
    · exact (h.chars.heckeα.1.div' h.chars.heckeβ.1 :)
    · rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.T.hecke_character_of_idele_class F E σ h.base.cm X.ν hHecke
  have hexp : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
    intro z hz
    have h1 := h.chars.expα z hz
    have h2 := h.chars.expβ z hz
    show (((X.α z / X.β z : Circle)) : ℂ) = _
    rw [Circle.coe_div, h1, h2, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
    have hne' : piInf (B.emb w) z / (‖piInf (B.emb w) z‖ : ℂ) ≠ 0 :=
      div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne))
    rw [zpow_sub₀ hne']
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.T.split_prime_degree_one F E (splitPrime t) (by rw [splitPrime_under]; exact hv.2)
  refine GlobalTheory.T.hecke_value_not_finite_order F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ hexp) (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

end GlobalTheory.NuGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_at_uniformizer_not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  first | exact @GlobalTheory.NuGood.not_root_of_unity | exact GlobalTheory.NuGood.not_root_of_unity | (intros; apply GlobalTheory.NuGood.not_root_of_unity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.UnitaryPlaceSplit

theorem mix_mul {S A : Type} [CommRing S] [Ring A] [Algebra S A] {e : S} (he : e * e = e) (x y z w : A) :
    (e • x + (1 - e) • y) * (e • z + (1 - e) • w) = e • (x * z) + (1 - e) • (y * w) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h0, sub_zero]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, he, h0, h0', h1, zero_smul, add_zero,
    zero_add]

variable {F : Type} [Field F] [NumberField F]

def idemAt (v : Pl (F := F)) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)

theorem evFin_idemAt (v : Pl (F := F)) : evFin F v (idemAt v) = 1 := evalV_singleFin_self v 1

theorem idemAt_mul_self (v : Pl (F := F)) : idemAt v * idemAt v = idemAt v := by
  refine Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero 0) ?_
  change singleFin v 1 * singleFin v 1 = singleFin v 1
  rw [← singleFin_mul, one_mul]

theorem mul_idemAt_of_evFin (v : Pl (F := F)) {u : AF F} (hu : evFin F v u = 0) : u * idemAt v = 0 := by
  refine Prod.ext (show u.1 * (0 : Ainf F) = 0 from mul_zero _) ?_
  change u.2 * singleFin v 1 = 0
  refine af_ext fun w => ?_
  rw [map_mul, map_zero]
  by_cases h : w = v
  · subst h
    have : evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [evalV_singleFin_ne h, mul_zero]

end GlobalTheory.UnitaryPlaceSplit

end

namespace GlobalTheory.UnitaryPlaceSplit

open Matrix

theorem exists_split_at (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (g : UA σ J) :
    ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
      ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  have hee : idemAt v * idemAt v = idemAt v := idemAt_mul_self v
  set e : AF F := idemAt v with he_def
  set G : Matrix (Fin n) (Fin n) (AE F E) := ((g.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
    with hG
  set Gi : Matrix (Fin n) (Fin n) (AE F E) :=
    ((g.1⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) with hGi
  have hGGi : G * Gi = 1 := Units.mul_inv g.1
  have hGiG : Gi * G = 1 := Units.inv_mul g.1
  have split : ∀ X : Matrix (Fin n) (Fin n) (AE F E), X = e • X + (1 - e) • X := fun X => by
    rw [← add_smul, add_sub_cancel, one_smul]
  set M : Matrix (Fin n) (Fin n) (AE F E) := e • G + (1 - e) • 1 with hM
  set N : Matrix (Fin n) (Fin n) (AE F E) := e • Gi + (1 - e) • 1 with hN
  have hMN : M * N = 1 := by rw [hM, hN, mix_mul hee, hGGi, mul_one, ← split]
  have hNM : N * M = 1 := by rw [hM, hN, mix_mul hee, hGiG, mul_one, ← split]
  let g1gl : GL (Fin n) (AE F E) := ⟨M, N, hMN, hNM⟩
  have hmem : g1gl ∈ UG (cA σ) (incM F J) := by
    change Mᵀ * incM F J * M.map (cA σ) = incM F J
    have hg : Gᵀ * incM F J * G.map (cA σ) = incM F J := g.2
    have hT : Mᵀ = e • Gᵀ + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [hM, transpose_add, transpose_smul, transpose_smul, transpose_one]
    have hc : M.map (cA σ) = e • G.map (cA σ) + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← AlgHom.mapMatrix_apply, hM, map_add (f := _), map_smul, map_smul, map_one, AlgHom.mapMatrix_apply]
    rw [hT, hc, split (incM F J), mix_mul hee, mix_mul hee, hg, one_mul, mul_one]
  let g₁ : UA σ J := ⟨g1gl, hmem⟩
  have hm1 : mat g₁ - 1 = e • (G - 1) := by
    change M - 1 = _
    rw [hM, smul_sub, sub_smul, one_smul]
    abel
  have hm2 : mat (g₁⁻¹ * g) - 1 = (1 - e) • (G - 1) := by
    change N * G - 1 = _
    conv_lhs => rw [split G]
    rw [hN, mix_mul hee, hGiG, one_mul, smul_sub, sub_smul (1 : AF F) e (1 : Matrix (Fin n) (Fin n) (AE F E)), one_smul]
    abel
  refine ⟨g₁, g₁⁻¹ * g, (mul_inv_cancel_left g₁ g).symm, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hm1, smul_smul, mul_idemAt_of_evFin v hu, zero_smul]
  · have h1 : (1 - e) • u = 0 := hu (1 - e) (by rw [map_sub, map_one, he_def, evFin_idemAt, sub_self])
    rw [hm2, smul_smul, mul_comm, ← smul_eq_mul, h1, zero_smul]

end GlobalTheory.UnitaryPlaceSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecompositionStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_place_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (g : UA σ J), ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
    ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  first | exact @GlobalTheory.UnitaryPlaceSplit.exists_split_at | exact GlobalTheory.UnitaryPlaceSplit.exists_split_at | (intros; apply GlobalTheory.UnitaryPlaceSplit.exists_split_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open Formalism.BasicNotions.TH

namespace GlobalTheory.FockQuot

variable (P Q R S : ℕ)

def rel (x : ℚ) : Submodule ℂ (Pol P Q R S) :=
  Submodule.span ℂ {g | ∃ (X : Mat P Q) (f : Pol P Q R S), g = fockAct1 P Q R S X f - ((x : ℂ) * X.trace) • f}

def act2 (t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S) :=
  fockAct2 P Q R S + (Matrix.traceLinearMap (Ix R S) ℂ ℂ).smulRight ((t : ℂ) • (1 : Module.End ℂ (Pol P Q R S)))

theorem fockSecondActionTraceShift_apply (t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    act2 P Q R S t Y f = fockAct2 P Q R S Y f + ((t : ℂ) * Y.trace) • f := by
  simp [act2, mul_comm, smul_smul]

theorem fockTraceCharacterRelations_le_comap_secondAction (x t : ℚ) (Y : Mat R S) : rel P Q R S x ≤ (rel P Q R S x).comap (act2 P Q R S t Y) := by
  refine Submodule.span_le.2 ?_
  rintro g ⟨X, f, rfl⟩
  have hc : fockAct2 P Q R S Y (fockAct1 P Q R S X f) = fockAct1 P Q R S X (fockAct2 P Q R S Y f) :=
    (LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.2 X Y) f).symm
  refine Submodule.subset_span ⟨X, act2 P Q R S t Y f, ?_⟩
  simp only [fockSecondActionTraceShift_apply, map_sub, map_add (f := _), map_smul, hc]

theorem isLieAct_fockSecondActionTraceShift (t : ℚ) : IsLieAct (act2 P Q R S t) := by
  intro X Y
  refine LinearMap.ext fun f => ?_
  have h := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.1 X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, fockSecondActionTraceShift_apply, map_add (f := _), map_smul, h, Matrix.trace_sub,
    Matrix.trace_mul_comm X Y, sub_self, mul_zero, zero_smul, add_zero]
  module

def actQ (x t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S ⧸ rel P Q R S x) where
  toFun Y := (rel P Q R S x).mapQ (rel P Q R S x) (act2 P Q R S t Y) (fockTraceCharacterRelations_le_comap_secondAction P Q R S x t Y)
  map_add' Y Z := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]
  map_smul' c Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]

theorem actQ_mk (x t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    actQ P Q R S x t Y (Submodule.Quotient.mk f) = Submodule.Quotient.mk (act2 P Q R S t Y f) := rfl

theorem actQ_lie (x t : ℚ) : IsLieAct (actQ P Q R S x t) := by
  intro X Y
  refine LinearMap.ext fun v => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have h := LinearMap.congr_fun (isLieAct_fockSecondActionTraceShift P Q R S t X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h ⊢
  simp only [actQ_mk, h, Submodule.Quotient.mk_sub]

theorem actQ_kfin (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    ∃ W : Submodule ℂ (Pol P Q R S ⧸ rel P Q R S x), FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (actQ P Q R S x t) W := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨W₀, hW₀, hf, hst⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  refine ⟨W₀.map (rel P Q R S x).mkQ, inferInstance, ⟨f, hf, rfl⟩, ?_⟩
  rintro X hX _ ⟨w, hw, rfl⟩
  refine ⟨act2 P Q R S t X w, ?_, rfl⟩
  rw [fockSecondActionTraceShift_apply]
  exact W₀.add_mem (hst X hX w hw) (W₀.smul_mem _ hw)

theorem actQ_wt (x t : ℚ) (μ : Ix R S → ℚ) (g : Pol P Q R S) (hg : g ∈ wtSub (fockAct2 P Q R S) μ) :
    (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈ wtSub (actQ P Q R S x t) (fun a => μ a + t) := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hg ⊢
  intro a
  rw [actQ_mk, fockSecondActionTraceShift_apply, hg a]
  simp [Eab, Matrix.trace_single_eq_same, add_smul]

theorem actQ_wts (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    v ∈ ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hf := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).2
  refine Submodule.iSup_induction (fun μ => wtSub (fockAct2 P Q R S) μ)
    (motive := fun g => (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈
      ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ) hf ?_ ?_ ?_
  · intro μ g hg
    exact Submodule.mem_iSup_of_mem _ (actQ_wt P Q R S x t μ g hg)
  · simp
  · intro g h hg hh
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ hg hh

def gkQ (x t : ℚ) : GKMod R S where
  V := Pol P Q R S ⧸ rel P Q R S x
  act := actQ P Q R S x t
  lie := actQ_lie P Q R S x t
  kfin := actQ_kfin P Q R S x t
  wts := actQ_wts P Q R S x t

theorem mk_fockFirstAction_eq_trace_smul (x : ℚ) (X : Mat P Q) (f : Pol P Q R S) :
    (Submodule.Quotient.mk (fockAct1 P Q R S X f) : Pol P Q R S ⧸ rel P Q R S x) =
      ((x : ℂ) * X.trace) • Submodule.Quotient.mk f := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨X, f, rfl⟩

end GlobalTheory.FockQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersAgreeInertUnramified
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertChars

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_mul_of_at {v : Pl (F := F)} {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hy : At (evFin F v) y) :
    y = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.EmbChart.atPlace v 1) * y := by
  have h0 : evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h1 : (1 - GlobalTheory.EmbChart.atPlace v 1) • y = 0 := hy _ h0
  rw [Algebra.smul_def, map_sub, map_one, sub_mul, one_mul, sub_eq_zero] at h1
  exact h1

private lemma tensorProduct_map_eq_zero_of_at_of_atPlace_eq_zero {R : Type} [CommRing R] [Algebra F R] {v : Pl (F := F)} (φ : AF F →ₐ[F] R)
    (hφ : φ (GlobalTheory.EmbChart.atPlace v 1) = 0) {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hy : At (evFin F v) y) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) y = 0 := by
  rw [eq_mul_of_at hy, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul,
    Algebra.algebraMap_self_apply, hφ, TensorProduct.zero_tmul, zero_mul]

theorem eq_ideleAt_of_at {v : Pl (F := F)} (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (hz : At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1)) :
    z = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v z) := by
  have hev : ∀ {R : Type} [CommRing R] [Algebra F R] (φ : AF F →ₐ[F] R), φ (GlobalTheory.EmbChart.atPlace v 1) = 0 →
      Algebra.TensorProduct.map φ (AlgHom.id F E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := by
    intro R _ _ φ hφ
    have h := tensorProduct_map_eq_zero_of_at_of_atPlace_eq_zero φ hφ hz
    rwa [map_sub, map_one, sub_eq_zero] at h
  apply GlobalTheory.Doubling.idele_ext
  · intro w
    rw [GlobalTheory.Doubling.unitInf_ideleAt]
    ext
    refine hev (evInf F w) ?_
    rw [GlobalTheory.EmbChart.atPlace_apply]
    show GlobalTheory.AutFunCompare.evW w (fstA F (pairA F 0 (singleFin v 1))) = 0
    exact map_zero _
  · intro u
    by_cases huv : u = v
    · subst huv
      rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
    · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne huv]
      ext
      refine hev (evFin F u) ?_
      rw [GlobalTheory.EmbChart.atPlace_apply]
      exact evalV_singleFin_ne huv 1

end GlobalTheory.InertChars

namespace GlobalTheory.InertChars

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locIdele_eq_of_inert {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (α β : Chr F E) (hres : ∀ b : (AF F)ˣ, α (ideleMap F E b) = β (ideleMap F E b))
    (hα : UnrAt α w) (hβ : UnrAt β w) (y : (w.adicCompletion E)ˣ) :
    α (locIdele F w y) = β (locIdele F w y) := by
  unfold UnrAt at hα hβ
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  obtain ⟨a, ha⟩ := GlobalTheory.LFun.InertValue.exists_isUnifAt hw h
  have hπ : α (locIdele F w (Units.map (complMap h).toMonoidHom a)) =
      β (locIdele F w (Units.map (complMap h).toMonoidHom a)) := by
    rw [GlobalTheory.LFun.InertValue.locIdele_complMap hw h a]
    exact hres _
  generalize Units.map (complMap h).toMonoidHom a = π at ha hπ
  have hunit : ∀ u : (w.adicCompletion E)ˣ, Valued.v (u : w.adicCompletion E) = 1 →
      α (locIdele F w u) = β (locIdele F w u) := by
    intro u hu
    have h1 : locChar α w u = 1 := hα u hu
    have h2 : locChar β w u = 1 := hβ u hu
    rw [← h2] at h1
    have h3 := congrArg (fun x : ℂˣ => (x : ℂ)) h1
    simp only [locChar, MonoidHom.comp_apply, Circle.toUnits_apply, Units.val_mk0] at h3
    exact Circle.ext h3
  have key : ∀ (u : (w.adicCompletion E)ˣ) (n : ℤ), Valued.v (u : w.adicCompletion E) = 1 →
      α (locIdele F w (u * π ^ n)) = β (locIdele F w (u * π ^ n)) := by
    intro u n hu'
    rw [map_mul, map_mul, map_mul, map_zpow, map_zpow, map_zpow, hunit u hu', hπ]
  have hy0 : Valued.v (y : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (y : w.adicCompletion E) = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hy0).symm⟩
  have hu : Valued.v ((y * π ^ k : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    have hπv : Valued.v (π : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := ha
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπv, hk, ← WithZero.exp_zsmul,
      ← WithZero.exp_add, smul_neg, smul_eq_mul, mul_one, add_neg_cancel, WithZero.exp_zero]
  have hy : y = (y * π ^ k) * π ^ (-k) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hy]
  exact key _ _ hu

theorem beta_eq_alpha_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
      ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → X.β z = X.α z := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv z hz
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have hpow : ((-1 : ℂ)) ^ a = (-1) ^ a' := by
    have he := hT.geo.even
    rw [Nat.even_add] at he
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, (he.mp ha).neg_one_pow]
    · have ha' : Odd a' := Nat.not_even_iff_odd.mp (fun h' => Nat.not_even_iff_odd.mpr ha (he.mpr h'))
      rw [ha.neg_one_pow, ha'.neg_one_pow]
  have hres : ∀ b : (AF F)ˣ, X.β (ideleMap F E b) = X.α (ideleMap F E b) := by
    intro b
    have e1 : ((X.α (ideleMap F E b) : Circle) : ℂ) = _ := hT.chars.resα b
    have e2 : ((X.β (ideleMap F E b) : Circle) : ℂ) = _ := hT.chars.resβ b
    apply Circle.ext
    rw [e1, e2, hpow]
  have hnot : ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl (F := F)))) := by
    rw [h]
    exact hv
  rw [eq_ideleAt_of_at z hz, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw]
  exact locIdele_eq_of_inert hw X.β X.α hres (hT.chars.unrβ w hnot) (hT.chars.unrα w hnot) _

end GlobalTheory.InertChars
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open IsDedekindDomain

namespace GlobalTheory.ArchimedeanL2

theorem lintegral_eq_of_fibres {Z X Y : Type} [AddGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [AddGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] (e : Z ≃ₜ+ X × Y) (μ : Measure Z) [μ.IsAddHaarMeasure]
    (ν : Measure X) [ν.IsAddHaarMeasure] {G G' : X × Y → ENNReal} (hG : Measurable G) (hG' : Measurable G')
    (h : ∀ y, ∫⁻ x, G (x, y) ∂ν = ∫⁻ x, G' (x, y) ∂ν) : ∫⁻ z, G (e z) ∂μ = ∫⁻ z, G' (e z) ∂μ := by
  have he : Measurable e := e.continuous.measurable
  let ρ : Measure Y := Measure.addHaar
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  haveI : (ν.prod ρ).IsAddHaarMeasure := inferInstance
  rw [← lintegral_map hG he, ← lintegral_map hG' he, Measure.isAddLeftInvariant_eq_smul (μ.map e) (ν.prod ρ),
    lintegral_smul_measure, lintegral_smul_measure, lintegral_prod_symm _ hG.aemeasurable,
    lintegral_prod_symm _ hG'.aemeasurable]
  simp only [h]

theorem lintegral_sq_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] (g : SchwartzMap V ℂ) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (g x) * g x ∂ν).re := by
  have hi : Integrable (fun x => ‖g x‖ ^ 2) ν := (g.memLp 2 ν).integrable_norm_pow (by norm_num)
  have h1 : ∀ x, star (g x) * g x = ((‖g x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h1]
  rw [integral_complex_ofReal, Complex.ofReal_re,
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable {F : Type} [Field F] [NumberField F]

theorem cont_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem cont_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm


variable (F) in
def splitEquiv (κ : Type) : (κ → AF F) ≃ₜ+ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl
  right_inv p := Prod.ext (funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _) rfl
  map_add' x y := Prod.ext (funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (y i).1) rfl
  continuous_toFun := (continuous_pi fun i => cont_toMixed.comp (continuous_fst.comp (continuous_apply i))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i =>
    (cont_ofMixed.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

theorem lintegral_arch_eq : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : SInf F κ →ₗ[ℂ] SInf F κ) (Ω : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ (f : SInf F κ) (h : (κ → Af F) → ℂ), Ω (pureA F f h) = pureA F (L f) h) →
    (∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
      ∫ x, star (L f₁ x) * L f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖Ω φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ L Ω hΩ hL μ hμ φ hφ
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ → Af F) := borel _
  haveI : BorelSpace (κ → Af F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hφ
  choose f h hh hg using fun i => (g i).2
  let ν : Measure (κ → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hB : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  have hν : ν.IsAddHaarMeasure := inferInstance
  have hsq : ∀ u : SInf F κ, ∫⁻ x, ‖u x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (u x) * u x ∂ν).re := fun u =>
    @lintegral_sq_eq (κ → mixedEmbedding.mixedSpace F) _ _ _ _ hB ν hν u
  haveI : OpensMeasurableSpace ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
    (Prod.borelSpace (α := κ → mixedEmbedding.mixedSpace F) (β := κ → Af F)).opensMeasurable
  have hm : ∀ u : Fin n → SInf F κ, Measurable fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) =>
      ‖∑ i, c i * (u i p.1 * h i p.2)‖ₑ ^ 2 := fun u =>
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      (((u i).continuous.comp continuous_fst).mul ((hh i).1.continuous.comp continuous_snd))).measurable.enorm.pow_const 2
  have hs : ∀ (u : Fin n → SInf F κ) (y : κ → Af F) (x : κ → mixedEmbedding.mixedSpace F),
      ∑ i, c i * (u i x * h i y) = (∑ i, (c i * h i y) • u i) x := fun u y x => by
    rw [sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_apply, smul_eq_mul]; ring
  have key := lintegral_eq_of_fibres (splitEquiv F κ) μ ν (hm fun i => L (f i)) (hm f) fun y => by
    simp only [hs]
    have e : ∑ i, (c i * h i y) • L (f i) = L (∑ i, (c i * h i y) • f i) := by simp only [map_sum, map_smul]
    rw [e, hsq, hsq, hL ν hν]
  have e1 : Ω (∑ i, c i • (g i : (κ → AF F) → ℂ)) = ∑ i, c i • pureA F (L (f i)) (h i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hg, hΩ]
  rw [e1]
  simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact key

end GlobalTheory.ArchimedeanL2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2Statement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_unitary_adelic_L2 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : SInf F κ →ₗ[ℂ] SInf F κ) (Ω : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ (f : SInf F κ) (h : (κ → Af F) → ℂ), Ω (pureA F f h) = pureA F (L f) h) →
    (∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
      ∫ x, star (L f₁ x) * L f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖Ω φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchimedeanL2.lintegral_arch_eq | exact GlobalTheory.ArchimedeanL2.lintegral_arch_eq | (intros; apply GlobalTheory.ArchimedeanL2.lintegral_arch_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdOfDvdIterates
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

noncomputable section

namespace GlobalTheory.MuDivides

private theorem mem_span_pow_smul_univ_iff_dvd {R : Type} [CommRing R] (q x : R) (n : ℕ) :
    x ∈ (Ideal.span {q} ^ n • ⊤ : Submodule R R) ↔ q ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem dvd_of_step {R : Type} [CommRing R] (q a : R) [IsAdicComplete (Ideal.span {q}) R]
    (P : R → Prop) (h : ∀ z, P z → ∃ y z₁, z = a * y + q * z₁ ∧ P z₁) (z : R) (hz : P z) :
    a ∣ z := by
  choose Y Z hYZ using h

  let s : ℕ → {w : R // P w} := fun n =>
    Nat.rec ⟨z, hz⟩ (fun _ w => ⟨Z w.1 w.2, (hYZ w.1 w.2).2⟩) n
  obtain ⟨w, y, hw0, hw⟩ : ∃ w y : ℕ → R, w 0 = z ∧ ∀ n, w n = a * y n + q * w (n + 1) :=
    ⟨fun n => (s n).1, fun n => Y (s n).1 (s n).2, rfl, fun n => (hYZ _ _).1⟩

  have key : ∀ n, z = a * (∑ k ∈ Finset.range n, q ^ k * y k) + q ^ n * w n := by
    intro n
    induction n with
    | zero => simp [hw0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hw n]
      ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {q}) (M := R) inferInstance
    (f := fun n => ∑ k ∈ Finset.range n, q ^ k * y k) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_span_pow_smul_univ_iff_dvd]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨-∑ j ∈ Finset.range d, q ^ j * y (m + j), ?_⟩
      rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
      simp only [pow_add, mul_assoc, sub_add_cancel_left])
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {q}) (M := R) inferInstance _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_span_pow_smul_univ_iff_dvd]
  have hn := hL n
  rw [SModEq.sub_mem, mem_span_pow_smul_univ_iff_dvd] at hn
  obtain ⟨c, hc⟩ := hn
  exact ⟨a * c + w n, by linear_combination key n + a * hc⟩

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]


omit [IsAlgClosed C] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem modP_isNilpotent_of_not_isUnit (hv : v.Integers O) (x : ModP O p) (hx : ¬IsUnit x) : IsNilpotent x := by
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O)}) x

  have hlt : v (algebraMap O C o) < 1 := by
    refine lt_of_le_of_ne (hv.map_le_one o) fun h1 => hx ?_
    exact (hv.isUnit_of_one' h1).map _

  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast]
    exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hp0 hlt
  refine ⟨n, ?_⟩
  have hdvd : (p : O) ∣ o ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hdvd)


omit [IsAlgClosed C] [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem eq_zero_of_forall_pow_dvd (hv : v.Integers O) (c m : PreTilt O p) (hc : ¬IsUnit c)
    (h : ∀ n, c ^ p ^ n ∣ m) : m = 0 := by
  have h0 : ¬IsUnit (PreTilt.coeff 0 c) := fun hu => hc (GlobalTheory.AinfXi.isUnit_of_coeff_zero hu)
  obtain ⟨N, hN⟩ := modP_isNilpotent_of_not_isUnit hv _ h0
  refine Perfection.ext (R := ModP O p) (p := p) fun k => ?_
  rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, map_zero]
  obtain ⟨d, hd⟩ := h (k + N)

  rw [hd, map_mul, map_pow, pow_add, pow_mul, GlobalTheory.AinfXi.coeff_pow_pow_zero,
    pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le hN, zero_mul]

omit [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem root_iterate_pow (n : ℕ) (ε : PreTilt O p) : (root^[n] ε) ^ p ^ n = ε :=
  iterate_frobeniusEquiv_symm_pow_p_pow (PreTilt O p) p ε n

theorem tilt_dvd (hv : v.Integers O) (ε : PreTilt O p) (hm : ε - 1 ≠ 0) (w : PreTilt O p)
    (h : ∀ n : ℕ, ε - 1 ∣ (root^[n] ε - 1) * w) : ε - 1 ∣ w := by
  obtain ⟨hD, hV⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv

  have ht : ∀ n : ℕ, (root^[n] ε - 1) ^ p ^ n = ε - 1 := fun n => by
    rw [sub_pow_char_pow, one_pow, root_iterate_pow]
  rcases ValuationRing.dvd_total (ε - 1) w with hw | ⟨u, hu⟩
  · exact hw
  by_cases hu' : IsUnit u
  · exact hu'.dvd_mul_right.1 (by rw [← hu])

  exfalso
  refine hm (eq_zero_of_forall_pow_dvd hv u (ε - 1) hu' fun n => ?_)
  have h1 : (ε - 1) * u ∣ (ε - 1) * (root^[n] ε - 1) := by
    have := mul_dvd_mul_right (h n) u
    rwa [mul_assoc, ← hu, mul_comm (root^[n] ε - 1)] at this
  have hut : u ∣ root^[n] ε - 1 := (mul_dvd_mul_iff_left hm).1 h1
  simpa only [ht n] using pow_dvd_pow_of_dvd hut (p ^ n)

omit [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem constantCoeff_mu (ε : PreTilt O p) : WittVector.constantCoeff (mu ε) = ε - 1 := by
  rw [mu, map_sub, map_one,
    show WittVector.constantCoeff (WittVector.teichmuller p ε) = ε from
      WittVector.teichmuller_coeff_zero p ε]

omit [IsAdicComplete (Ideal.span {(p : O)}) O] in
theorem exists_eq_p_mul (x : Ainf p O) (hx : WittVector.constantCoeff x = 0) :
    ∃ y, x = (p : Ainf p O) * y :=
  Ideal.mem_span_singleton.1 ((WittVector.mem_span_p_iff_coeff_zero_eq_zero x).2 hx)

theorem dvd_of_dvd_p_mul (hv : v.Integers O) (ε : PreTilt O p) (hm : ε - 1 ≠ 0) (w : Ainf p O)
    (h : mu ε ∣ (p : Ainf p O) * w) : mu ε ∣ w := by
  obtain ⟨hD, -⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv
  obtain ⟨c, hc⟩ := h

  have hc0 : WittVector.constantCoeff c = 0 := by
    have h0 := congrArg WittVector.constantCoeff hc
    rw [map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, constantCoeff_mu] at h0
    exact (mul_eq_zero.1 h0.symm).resolve_left hm
  obtain ⟨c', rfl⟩ := exists_eq_p_mul c hc0
  refine ⟨c', sub_eq_zero.1 (WittVector.eq_zero_of_p_mul_eq_zero _ ?_)⟩
  linear_combination hc

theorem mu_dvd_of_forall_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ z : Ainf p O, (∀ n : ℕ, mu ε ∣ mu (root^[n] ε) * z) → mu ε ∣ z := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε z hz
  have hm : ε - 1 ≠ 0 := by
    rw [← constantCoeff_mu]
    exact (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).1
  refine dvd_of_step (p : Ainf p O) (mu ε) (fun x => ∀ n : ℕ, mu ε ∣ mu (root^[n] ε) * x) ?_ z hz
  intro x hx

  obtain ⟨b, hb⟩ : ε - 1 ∣ WittVector.constantCoeff x := by
    refine tilt_dvd hv ε hm _ fun n => ?_
    have h1 := map_dvd WittVector.constantCoeff (hx n)
    rwa [map_mul, constantCoeff_mu, constantCoeff_mu] at h1

  obtain ⟨z₁, hz₁⟩ := exists_eq_p_mul (x - mu ε * WittVector.teichmuller p b) (by
    rw [map_sub, map_mul, constantCoeff_mu, hb, sub_eq_zero,
      show WittVector.constantCoeff (WittVector.teichmuller p b) = b from
        WittVector.teichmuller_coeff_zero p b])
  refine ⟨WittVector.teichmuller p b, z₁, by rw [← hz₁]; ring, fun n => ?_⟩

  apply dvd_of_dvd_p_mul hv ε hm
  have h1 : mu ε ∣ mu (root^[n] ε) * (x - mu ε * WittVector.teichmuller p b) := by
    rw [mul_sub]
    exact dvd_sub (hx n) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  rwa [hz₁, mul_left_comm] at h1

end GlobalTheory.MuDivides
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SkewDet

theorem det_ne_zero_of_isSkew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → W.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B n r s W hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := hW.sig w
  subst hrs
  intro hdet
  set φ : E →+* ℂ := (B.emb w).1
  set M : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := Complex.I • W.J.map φ with hM
  have hMdet : M.det = 0 := by
    rw [hM, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero, mul_zero]
  set P : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have hP : Pᵀ * M * P.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]
    ext i j
    simp [P, Matrix.mul_apply]
  have h2 := congrArg Matrix.det hP
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, hMdet, mul_zero, zero_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg] at h2
  rw [Matrix.det_one, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

end GlobalTheory.SkewDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_ne_zero_of_skewHermitianSelfDualLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → W.J.det ≠ 0 := by
  first | exact @GlobalTheory.SkewDet.det_ne_zero_of_isSkew | exact GlobalTheory.SkewDet.det_ne_zero_of_isSkew | (intros; apply GlobalTheory.SkewDet.det_ne_zero_of_isSkew <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithGlobalMaximumPrincipleOffDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithGlobalMaximumPrincipleOffDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem max_principle_global : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ρ ≤ P.nu 0 1 σ y s → P.nu N 0 σ y f ≤ R) → f ∈ P.Bl N 0 (Real.exp (δ * N) * R) := by
  intro k _ X _ p D hX P s hs hs0 δ hδ
  classical
  choose W ρ hW hρ H using GlobalTheory.T.exists_nhds_nu_le_exp_mul_of_far_bound k X p D hX P s hs hs0 δ hδ
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  have hcov : ∀ σ : k →+* ℂ, ∃ t : Finset (CxPts p σ), (Set.univ : Set (CxPts p σ)) ⊆ ⋃ x ∈ t, W σ x := by
    intro σ
    haveI : CompactSpace (CxPts p σ) := hX.compactSpace σ
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (W σ) (fun x _ => hW σ x)
    exact ⟨t, ht⟩
  choose t ht using hcov
  have hlow : ∀ {ι : Type} [Finite ι] (g : ι → ℝ), (∀ i, 0 < g i) → ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ g i := by
    intro ι _ g hg
    rcases isEmpty_or_nonempty ι with h | h
    · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
    · obtain ⟨i, hi⟩ := Finite.exists_min g
      exact ⟨g i, hg i, hi⟩
  obtain ⟨c, hc, hcle⟩ := hlow (ι := Σ σ : k →+* ℂ, {x // x ∈ t σ}) (fun z => ρ z.1 z.2.1) (fun z => hρ _ _)
  refine ⟨c, hc, fun N f R hf hR => ⟨hf, fun σ y => ?_⟩⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht σ (Set.mem_univ y))
  exact H σ x N f R hf (fun σ' y' h => hR σ' y' ((hcle ⟨σ, ⟨x, hx⟩⟩).trans h)) y hy

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithGlobalMaximumPrincipleOffDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_global_maximum_principle_off_divisor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ρ ≤ P.nu 0 1 σ y s → P.nu N 0 σ y f ≤ R) → f ∈ P.Bl N 0 (Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.VolBr.max_principle_global | exact GlobalTheory.VolBr.max_principle_global | (intros; apply GlobalTheory.VolBr.max_principle_global <;> assumption)
end
end
