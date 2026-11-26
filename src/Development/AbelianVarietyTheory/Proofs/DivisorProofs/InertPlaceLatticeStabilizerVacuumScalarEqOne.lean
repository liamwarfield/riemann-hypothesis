module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInertPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSupportedAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTransformingCharacterEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumNotMemAugmentationInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOfHeisInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormCompLocalWeilOperatorStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormCompLocalWeilOperator
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacEquiv

theorem acts_schr_of_ref {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ)
    (w : (κ → AF F) × (κ → AF F)) (h₁ : At (evFin F v) w.1) (h₂ : At (evFin F v) w.2)
    (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0) (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x)
    (φ φ₁ : (κ → Fv F v) → ℂ) (h : schr ψ w (tens (evFin F v) φ R) = tens (evFin F v) φ₁ R) :
    Acts (evFin F v) (schr ψ w) φ φ₁ := by
  intro r hr
  funext x
  set y : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (x i)) with hyD
  have hev : ∀ i, evFin F v (y i) = evFin F v (x i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have hy : At (evFin F v) y := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hRy : R y = R 0 := by simpa using hR 0 y hy
  have hRyw : R (y + w.1) = R y := hR y w.1 h₁
  have hrx : r (x + w.1) = r x := hr.1 x w.1 h₁
  have hdot : x ⬝ᵥ w.2 = y ⬝ᵥ w.2 := by
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    have hz : evFin F v (x i - y i) = 0 := by rw [map_sub, hev, sub_self]
    have h0 := congrFun (h₂ (x i - y i) hz) i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    rw [← sub_eq_zero, ← sub_mul, h0]
  have hφ : (fun i => evFin F v ((x + w.1) i)) = (fun i => evFin F v ((y + w.1) i)) := by
    funext i
    simp only [Pi.add_apply, map_add (f := _), hev]
  have hφ₁ : (fun i => evFin F v (x i)) = (fun i => evFin F v (y i)) := by
    funext i
    exact (hev i).symm
  have key := congrFun h y
  simp only [schr, tens] at key ⊢
  rw [hRyw, hRy] at key
  rw [hdot, hrx, hφ₁]
  have hcanc : ψ (y ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * φ (fun i => evFin F v ((x + w.1) i)) =
      φ₁ (fun i => evFin F v (y i)) := by
    apply mul_right_cancel₀ hR0
    rw [hφ, ← key, mul_assoc]
  rw [← mul_assoc, hcanc]

theorem heisInv_comp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v m C l hl g _ S hS u hu φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hRest⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hsp := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  set u' := GlobalTheory.WeilM.actAB (cA σ) ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u with hu'D
  have hu'eq : u' = mat g * u := by
    simp [hu'D, GlobalTheory.WeilM.actAB, mat]
  obtain ⟨huAt, z, hz⟩ := hu
  have hAt' : At (evFin F v) u' := by
    intro c hc
    rw [hu'eq, ← Matrix.mul_smul, huAt c hc, Matrix.mul_zero]
  have hlag : u' ∈ GlobalTheory.InertVacLag.lagAt v C := ⟨hAt', mat g * z, by rw [hu'eq, hz, Matrix.mul_assoc]⟩
  have hco1 : At (evFin F v) (G.M'.co.e u').1 := by
    intro c hc
    rw [← Prod.smul_fst, ← map_smul, hAt' c hc, map_zero, Prod.fst_zero]
  have hco2 : At (evFin F v) (G.M'.co.e u').2 := by
    intro c hc
    rw [← Prod.smul_snd, ← map_smul, hAt' c hc, map_zero, Prod.snd_zero]
  have hRinv := (hRest 0 (Submodule.zero_mem _)).1
  have hact : Acts (evFin F v) (G.M'.co.rho B.ψ u') (S φ) (S φ₁) := by
    apply acts_schr_of_ref v B.ψ (G.M'.co.e u') hco1 hco2 R hR0 hRinv
    have e1 := (hS φ hφ).2 R (hRest φ hφ)
    have e2 := (hS φ₁ hφ₁).2 R (hRest φ₁ hφ₁)
    have e3 := hA R (hRest φ hφ)
    have e4 := hsp.impl ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u (tens (evFin F v) φ R) (hRest φ hφ).2
    show G.M'.co.rho B.ψ u' (tens (evFin F v) (S φ) R) = tens (evFin F v) (S φ₁) R
    rw [← e1, ← e2, ← e3, hu'D]
    exact e4.symm
  exact hl u' hlag (S φ) (hS φ hφ).1 (S φ₁) (hS φ₁ hφ₁).1 hact

end GlobalTheory.InertVacEquiv
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  first | exact @GlobalTheory.InertVacEquiv.heisInv_comp | exact GlobalTheory.InertVacEquiv.heisInv_comp | (intros; apply GlobalTheory.InertVacEquiv.heisInv_comp <;> assumption)
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacLag

theorem inv_of_heisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = l φ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hv m C hC l hl g hg φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin a' × Fin (a + a')) v
  have htadd : ∀ f f' : (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      tens (evFin F v) (f + f') R = tens (evFin F v) f R + tens (evFin F v) f' R := fun f f' => by
    funext x; simp [tens, add_mul]
  have htsmul : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) R = c • tens (evFin F v) f R := fun c f => by
    funext x; simp [tens, mul_assoc]
  let Sop : UA σ G.V'.J → (((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ)) :=
    fun g =>
    { toFun := fun f t => (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i))
      map_add' := fun f f' => by
        funext t; simp only [htadd, map_add (f := _), Pi.add_apply]; ring
      map_smul' := fun c f => by
        funext t; simp only [htsmul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hSop : ∀ g f t, Sop g f t = (R 0)⁻¹ * om' (g, 1) (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) :=
    fun _ _ _ => rfl
  have huniq : ∀ (T : ((Fin a' × Fin (a + a') → AF F) → ℂ) → (Fin a' × Fin (a + a') → AF F) → ℂ)
      (f f₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ SB _ → Acts (evFin F v) T f f₁ →
      ∀ t, f₁ t = (R 0)⁻¹ * T (tens (evFin F v) f R) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro T f f₁ hf hA t
    rw [hA R (hR f hf)]
    have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
      intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
    have h1 : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
      simpa using (hR f hf).1 0 _ hat
    simp only [tens, h1, GlobalTheory.LatVac.evFin_liftV]
    field_simp
  have hS : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Sop g f ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (g, 1)) f (Sop g f) := by
    intro g hg f hf
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v g hg
    have e : S₀ f = Sop g f := funext fun t => (huniq _ f _ hf (hS₀ f hf).2 t).trans (hSop g f t).symm
    rw [← e]; exact hS₀ f hf
  obtain ⟨φ₀, hφ₀, hline⟩ := GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test F E σ a' (a + a') G.V' G.W G.M' B.ψ v (hT.base.inert v w hin).2.2 m C hC
  by_cases hz : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), l f = 0
  · rw [hz φ₁ hφ₁, hz φ hφ]
  push_neg at hz
  have hl0 : l φ₀ ≠ 0 := fun h => by
    obtain ⟨f, hf, hne⟩ := hz; exact hne (hline l hl h f hf)
  let c : UA σ G.V'.J → ℂ := fun g => l (Sop g φ₀) / l φ₀
  have hlaw : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ f₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) f f₁ → l f₁ = c g * l f := by
    intro g hg f hf f₁ hf₁ hA
    have hf₁eq : f₁ = Sop g f := funext fun t => (huniq _ f f₁ hf hA t).trans (hSop g f t).symm
    have hE := GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator F E σ B a a' G X om om' hT v m C l hl g hg (Sop g) (hS g hg)
    have hl' : GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ Sop g - c g • l) := by
      intro u hu f hf f₁ hf₁ hA'
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hE u hu f hf f₁ hf₁ hA', hl u hu f hf f₁ hf₁ hA']
    have h0 : (l ∘ₗ Sop g - c g • l) φ₀ = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, c]
      field_simp
      ring
    have h1 := hline _ hl' h0 f hf
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at h1
    rw [hf₁eq]
    linear_combination h1
  have hc := GlobalTheory.T.inert_place_transforming_character_eq_one F E σ B a a' G X om om' hT v w hin hv m C hC l hl hz c hlaw g hg
  rw [hlaw g hg φ hφ φ₁ hφ₁ hA, hc, one_mul]

end GlobalTheory.InertVacLag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory

noncomputable section

namespace GlobalTheory.SchrSuppFin

theorem exists_nhds_translate_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [NonarchimedeanAddGroup V] {f : V → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ U ∈ nhds (0 : V), ∀ u ∈ U, ∀ z, f (z + u) = f z := by
  have hW : ∀ x : V, ∃ W : OpenAddSubgroup V, ∀ w ∈ (W : Set V), f (x + w) = f x := by
    intro x
    have h1 : {w : V | f (x + w) = f x} ∈ nhds (0 : V) := by
      have h2 := (hf.comp_continuous (show Continuous (fun w : V => x + w) from continuous_const.add continuous_id)).eventually_eq 0
      simp only [Function.comp, add_zero] at h2
      exact h2
    obtain ⟨W, hW⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h1
    exact ⟨W, fun w hw => hW hw⟩
  choose W hW using hW
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun x => {z : V | z - x ∈ (W x : Set V)}) (fun x _ => by
    refine (continuous_sub_right x).continuousAt.preimage_mem_nhds ?_
    simpa using (W x).isOpen.mem_nhds (W x).zero_mem)
  refine ⟨⋂ x ∈ t, (W x : Set V), (Filter.biInter_finset_mem t).2 fun x _ => (W x).isOpen.mem_nhds (W x).zero_mem,
    fun u hu z => ?_⟩
  simp only [Set.mem_iInter] at hu
  by_cases hz : ∃ x ∈ t, z - x ∈ (W x : Set V)
  · obtain ⟨x, hx, hzx⟩ := hz
    have e1 := hW x (z - x) hzx
    have e2 := hW x (z + u - x) (by
      rw [show z + u - x = (z - x) + u by abel]; exact (W x).add_mem hzx (hu x hx))
    rw [show x + (z - x) = z by abel] at e1
    rw [show x + (z + u - x) = z + u by abel] at e2
    rw [e1, e2]
  · push_neg at hz
    have h1 : z ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      exact hz x hx hzx
    have h2 : z + u ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      refine hz x hx ?_
      have := (W x).sub_mem hzx (hu x hx)
      rwa [show z + u - x - u = z - x by abel] at this
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem nhdsNE_neBot {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) : (nhdsWithin (0 : Fv F v) {0}ᶜ).NeBot := by
  refine ⟨fun h => ?_⟩
  have hopen : IsOpen ({0} : Set (Fv F v)) := (isOpen_singleton_iff_punctured_nhds _).2 h
  haveI := discreteTopology_of_isOpen_singleton_zero hopen
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hinf : ((v.adicCompletionIntegers F : Set (Fv F v))).Infinite :=
    Set.infinite_of_injective_forall_mem (Nat.cast_injective (R := Fv F v)) fun n => natCast_mem _ n
  exact hinf (hO.finite_of_discrete)

end GlobalTheory.SchrSuppFin

namespace GlobalTheory.SchrSuppFin

theorem support_compact : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  intro F _ _ v ψ₀ κ _ _ _ μ _ hψ hcond φ hφ g hg
  classical
  obtain ⟨hφl, hφc⟩ := hφ
  obtain ⟨hgl, hgc⟩ := hg
  obtain ⟨Uφ, hUφ, hφU⟩ := exists_nhds_translate_eq hφl hφc
  obtain ⟨Ug, hUg, hgU⟩ := exists_nhds_translate_eq hgl hgc
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  have hP : ∀ᶠ s in nhds (0 : Fv F v), ∀ y ∈ (v.adicCompletionIntegers F : Set (Fv F v)), ∀ i : κ,
      (Pi.single i (s * y) : κ → Fv F v) ∈ Uφ ∩ Ug := by
    refine hO.eventually_forall_of_forall_eventually fun y _ => ?_
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v) :=
      (continuous_single i).comp continuous_mul
    have hmem : Uφ ∩ Ug ∈ nhds ((fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v)) (0, y)) := by
      simpa using Filter.inter_mem hUφ hUg
    exact hc.continuousAt.preimage_mem_nhds hmem
  haveI := nhdsNE_neBot v
  obtain ⟨t, ht, ht0⟩ := ((hP.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (Fv F v))))).exists
  have ht0' : t ≠ 0 := ht0
  refine ⟨((fun p : (κ → Fv F v) × (κ → Fv F v) => p.1 - p.2) '' (tsupport φ ×ˢ tsupport g)) ×ˢ
    Set.pi Set.univ (fun _ => (fun y => t⁻¹ * y) '' (v.adicCompletionIntegers F : Set (Fv F v))), ?_, ?_⟩
  · exact ((hφc.isCompact.prod hgc.isCompact).image continuous_sub).prod
      (isCompact_univ_pi fun _ => hO.image (continuous_const_mul _))
  · rintro ⟨a, b⟩ hne
    have key : ∀ u ∈ Uφ ∩ Ug, ψ₀ (u ⬝ᵥ b) = 1 := by
      intro u hu
      have hG : ∀ y, schr ψ₀ (a, b) φ (y + u) * (starRingEnd ℂ) (g (y + u)) =
          ψ₀ (u ⬝ᵥ b) * (schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) := by
        intro y
        simp only [schr]
        rw [show y + u + a = (y + a) + u by abel, hφU u hu.1, hgU u hu.2, add_dotProduct,
          show y ⬝ᵥ b + u ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b) = u ⬝ᵥ b + (y ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b)) by ring,
          AddChar.map_add_eq_mul]
        ring
      have e := integral_add_right_eq_self (μ := μ)
        (fun y => schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) u
      simp only [hG] at e
      rw [integral_const_mul] at e
      have h0 : (ψ₀ (u ⬝ᵥ b) - 1) * ∫ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ∂μ = 0 := by
        rw [sub_mul, e]; ring
      exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hne)
    refine ⟨?_, ?_⟩
    · have hex : ∃ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (by simp [h])
      obtain ⟨y, hy⟩ := hex
      have h1 : φ (y + a) ≠ 0 := fun h => hy (by simp [schr, h])
      have h2 : g y ≠ 0 := fun h => hy (by simp [h])
      exact ⟨(y + a, y), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, by simp⟩
    · intro i _
      have hb : t * b i ∈ v.adicCompletionIntegers F := hcond _ fun y hy => by
        have := key _ (ht y hy i)
        rwa [single_dotProduct, show t * y * b i = t * b i * y by ring] at this
      exact ⟨t * b i, hb, by field_simp⟩

end GlobalTheory.SchrSuppFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFinStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  first | exact @GlobalTheory.SchrSuppFin.support_compact | exact GlobalTheory.SchrSuppFin.support_compact | (intros; apply GlobalTheory.SchrSuppFin.support_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistence
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

open MeasureTheory ComplexConjugate
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagLocForm

section
variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)}

theorem schr_adj (ψ₀ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ₀) {κ : Type} [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure]
    (w : (κ → Fv F v) × (κ → Fv F v)) (f g : (κ → Fv F v) → ℂ) :
    ∫ y, schr ψ₀ w f y * conj (g y) ∂μ = ∫ y, f y * conj (schr ψ₀ (-w) g y) ∂μ := by
  have h1 : ∀ s, conj (ψ₀ s) = ψ₀ (-s) := by
    intro s
    have h := GlobalTheory.norm_addChar_nonarch ψ₀ hψ s
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h]
    simp
  rw [← integral_add_right_eq_self (fun y => f y * conj (schr ψ₀ (-w) g y)) w.1]
  congr 1
  funext y
  have h2 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
  have e : -((y + w.1) ⬝ᵥ -w.2 + ⅟(2 : Fv F v) * (-w.1 ⬝ᵥ -w.2)) = y ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) := by
    simp only [add_dotProduct, dotProduct_neg, neg_dotProduct, neg_neg]
    linear_combination (-(w.1 ⬝ᵥ w.2)) * h2
  simp only [schr, Prod.fst_neg, Prod.snd_neg, map_mul, h1, add_neg_cancel_right]
  rw [e]; ring

theorem ip_self_ne {κ : Type} [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure] (g : (κ → Fv F v) → ℂ) (hg : g ∈ SB (κ → Fv F v))
    (h0 : g ≠ 0) : ∫ y, g y * conj (g y) ∂μ ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have e : (fun y => g y * conj (g y)) = fun y => ((Complex.normSq (g y) : ℝ) : ℂ) := by
    funext y; exact Complex.mul_conj (g y)
  rw [e, integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine ne_of_gt ?_
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := x)
    (Complex.continuous_normSq.comp hg.1.continuous) (hg.2.comp_left (g := Complex.normSq) (map_zero _))
    (fun y => Complex.normSq_nonneg _) ?_
  simpa using hx

end

theorem lagr_local_form : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  intro F _ _ v ψ₀ κ _ Λ Γ vac hψ hcond hiso hΓo hΓc hdual hvSB hv0 heig hfix
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  let μ : Measure (κ → Fv F v) := Measure.addHaar
  let c : ((κ → Fv F v) → ℂ) → ((κ → Fv F v) × (κ → Fv F v)) → ℂ :=
    fun φ w => ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ
  have hc : ∀ (φ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v)), c φ w = ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ := fun _ _ => rfl
  have schr_zero : ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ 0 φ = φ := by
    intro φ; funext x; simp [schr]
  have schr_add : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (φ₁ φ₂ : (κ → Fv F v) → ℂ), schr ψ₀ w (φ₁ + φ₂) = schr ψ₀ w φ₁ + schr ψ₀ w φ₂ := by
    intro w φ₁ φ₂; funext x; simp [schr, mul_add]
  have schr_smul : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (a : ℂ) (φ : (κ → Fv F v) → ℂ), schr ψ₀ w (a • φ) = a • schr ψ₀ w φ := by
    intro w a φ; funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  have comp_iso : ∀ w ∈ Λ, ∀ w' ∈ Λ, ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ w (schr ψ₀ w' φ) = schr ψ₀ (w + w') φ := by
    intro w hw w' hw' φ
    rw [GlobalTheory.ThetaQuasiRat.schr_schr, hiso w hw w' hw', mul_zero, AddChar.map_zero_eq_one, one_smul]

  have hconst : ∀ φ : (κ → Fv F v) → ℂ, ∀ l ∈ Λ, ∀ γ ∈ Γ, γ ∈ Λ → c φ (l + γ) = c φ l := by
    intro φ l hl γ hγ hγΛ
    rw [hc, hc, add_comm, ← comp_iso γ hγΛ l hl, schr_adj ψ₀ hψ μ γ (schr ψ₀ l φ) vac,
      hfix (-γ) (AddSubgroup.mem_inf.2 ⟨Γ.neg_mem hγ, Λ.neg_mem hγΛ⟩)]
  let H : AddSubgroup Λ := Γ.addSubgroupOf Λ
  let ct : ((κ → Fv F v) → ℂ) → Λ ⧸ H → ℂ := fun φ =>
    Quotient.lift (s := QuotientAddGroup.leftRel H) (fun l : Λ => c φ l) (by
      intro a b hab
      have hab : -a + b ∈ H := QuotientAddGroup.leftRel_apply.1 hab
      rw [AddSubgroup.mem_addSubgroupOf] at hab
      have e : (b : (κ → Fv F v) × (κ → Fv F v)) = a + ((-a + b : Λ) : (κ → Fv F v) × (κ → Fv F v)) := by
        simp
      show c φ a = c φ b
      rw [e, hconst φ a a.2 _ hab (-a + b).2])
  have hct : ∀ (φ : (κ → Fv F v) → ℂ) (l : Λ), ct φ (l : Λ ⧸ H) = c φ l := fun _ _ => rfl

  have hfin : ∀ φ ∈ SB (κ → Fv F v), (Function.support (ct φ)).Finite := by
    intro φ hφ
    obtain ⟨C, hCc, hC⟩ := GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace v ψ₀ κ μ hψ hcond φ hφ vac hvSB
    obtain ⟨t, ht⟩ := hCc.elim_finite_subcover (fun i : C => (fun z => z - (i : (κ → Fv F v) × (κ → Fv F v))) ⁻¹' Γ)
      (fun i => hΓo.preimage (continuous_sub_right _))
      (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, by simp [Set.mem_preimage, sub_self, zero_mem]⟩)
    refine Set.Finite.subset (t.finite_toSet.biUnion fun i _ =>
      (Set.Subsingleton.finite (s := (QuotientAddGroup.mk : Λ → Λ ⧸ H) ''
        {l : Λ | (l : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ}) ?_)) ?_
    · rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have := Γ.sub_mem (show (l₂ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₂)
        (show (l₁ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₁)
      simpa [sub_sub_sub_cancel_right, neg_add_eq_sub] using this
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H l =>
        rw [Function.mem_support, hct] at hq
        have hlC := hC _ hq
        obtain ⟨i, hi, hli⟩ := Set.mem_iUnion₂.1 (ht hlC)
        exact Set.mem_biUnion hi ⟨l, hli, rfl⟩
  have hint : ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v),
      Integrable (fun y => schr ψ₀ w φ y * conj (vac y)) μ := by
    intro w φ hφ
    have h1 := GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ
    exact (h1.1.continuous.mul (Complex.continuous_conj.comp hvSB.1.continuous)).integrable_of_hasCompactSupport
      (hvSB.2.comp_left (g := conj) (map_zero _)).mul_left
  have ct_add : ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), ct (φ₁ + φ₂) = ct φ₁ + ct φ₂ := by
    intro φ₁ h₁ φ₂ h₂
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.add_apply, hc, schr_add, add_mul]
      exact integral_add (hint _ _ h₁) (hint _ _ h₂)
  have ct_smul : ∀ (a : ℂ) (φ : (κ → Fv F v) → ℂ), ct (a • φ) = a • ct φ := by
    intro a φ
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.smul_apply, smul_eq_mul, hc, schr_smul, mul_assoc]
      exact integral_const_mul a _
  let l₀ : SB (κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∑ᶠ q, ct φ q
      map_add' := fun φ₁ φ₂ => by
        show ∑ᶠ q, ct ((φ₁ : (κ → Fv F v) → ℂ) + φ₂) q = ∑ᶠ q, ct φ₁ q + ∑ᶠ q, ct φ₂ q
        rw [ct_add _ φ₁.2 _ φ₂.2]
        exact finsum_add_distrib (hfin _ φ₁.2) (hfin _ φ₂.2)
      map_smul' := fun a φ => by
        show ∑ᶠ q, ct (a • (φ : (κ → Fv F v) → ℂ)) q = (RingHom.id ℂ) a • ∑ᶠ q, ct φ q
        rw [ct_smul, RingHom.id_apply, smul_eq_mul, mul_finsum]
        rfl }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  have hl' : ∀ φ (hφ : φ ∈ SB (κ → Fv F v)), l φ = ∑ᶠ q, ct φ q := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  refine ⟨l, fun w hw φ hφ => ?_, ?_⟩
  · rw [hl' _ (GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ), hl' φ hφ]
    have e : ct (schr ψ₀ w φ) = fun q => ct φ (q + ((⟨w, hw⟩ : Λ) : Λ ⧸ H)) := by
      funext q
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        rw [← QuotientAddGroup.mk_add, hct, hct, hc, hc, comp_iso m m.2 w hw]
        rfl
    rw [e]
    exact finsum_comp_equiv (Equiv.addRight _)
  · have hX0 : c vac 0 ≠ 0 := by
      rw [hc, schr_zero]; exact ip_self_ne μ vac hvSB hv0
    have hd : ∀ w, c vac w ≠ 0 → w ∈ Γ := by
      intro w hw
      rw [hdual]
      intro γ hγ
      obtain ⟨a, ha⟩ := heig γ hγ
      have hinv : a • schr ψ₀ (-γ) vac = vac := by
        rw [← schr_smul, ← ha, GlobalTheory.ThetaQuasiRat.schr_schr, neg_add_cancel, schr_zero]
        have : (-γ).1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ (-γ).2 = 0 := by
          simp only [Prod.fst_neg, Prod.snd_neg, neg_dotProduct, dotProduct_neg]; ring
        rw [this, mul_zero, AddChar.map_zero_eq_one, one_smul]
      have ha0 : a ≠ 0 := by
        rintro rfl; apply hv0; rw [← hinv, zero_smul]
      have hneg : schr ψ₀ (-γ) vac = a⁻¹ • vac := by
        rw [← hinv, smul_smul, inv_mul_cancel₀ ha0, one_smul, hinv]
      have key : ∀ w : (κ → Fv F v) × (κ → Fv F v),
          ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a * c vac w = conj a⁻¹ * c vac w := by
        intro w
        have e1 : schr ψ₀ γ (schr ψ₀ w vac) = (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) • schr ψ₀ w vac := by
          have h1 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ γ w vac
          have h2 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ w γ vac
          rw [ha, schr_smul, add_comm w γ] at h2
          rw [h1, mul_smul, h2, smul_smul, ← AddChar.map_add_eq_mul]
          have h3 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
          have e4 : ⅟(2 : Fv F v) * (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) =
              (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) := by
            linear_combination (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * h3
          rw [e4]
        have e3 : ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ =
            ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
          calc ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ
              = ∫ y, schr ψ₀ γ (schr ψ₀ w vac) y * conj (vac y) ∂μ := by
                congr 1; funext y; rw [e1, Pi.smul_apply, smul_eq_mul]; ring
            _ = ∫ y, schr ψ₀ w vac y * conj (schr ψ₀ (-γ) vac y) ∂μ := schr_adj ψ₀ hψ μ γ _ vac
            _ = ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
                congr 1; funext y; rw [hneg, Pi.smul_apply, smul_eq_mul, map_mul]; ring
        rw [integral_const_mul, integral_const_mul] at e3
        rw [hc]; exact e3
      have haa : a = conj a⁻¹ := by
        have k0 := key 0
        simp only [Prod.snd_zero, Prod.fst_zero, dotProduct_zero, zero_dotProduct, sub_zero,
          AddChar.map_zero_eq_one, one_mul] at k0
        exact mul_right_cancel₀ hX0 k0
      have hk := key w
      rw [← haa] at hk
      have hψω : ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) = 1 := by
        have := mul_right_cancel₀ hw hk
        exact mul_right_cancel₀ ha0 (by rw [this, one_mul])
      rw [show w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2 = -(γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) by ring, AddChar.map_neg_eq_inv, hψω, inv_one]
    rw [hl' vac hvSB, finsum_eq_single _ (0 : Λ ⧸ H)]
    · show ct vac ((0 : Λ) : Λ ⧸ H) ≠ 0
      rw [hct]; simpa using hX0
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        by_contra hm
        rw [hct] at hm
        exact hq ((QuotientAddGroup.eq_zero_iff m).2 (AddSubgroup.mem_addSubgroupOf.2 (hd m hm)))

end GlobalTheory.LagLocForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistenceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  first | exact @GlobalTheory.LagLocForm.lagr_local_form | exact GlobalTheory.LagLocForm.lagr_local_form | (intros; apply GlobalTheory.LagLocForm.lagr_local_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertVacLagP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_map_compFin (v : Pl (F := F)) {d m : ℕ} (Cy : Matrix (Fin d) (Fin m) (Fv F v ⊗[F] E)) :
    ∃ C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), C.map (compFin F E v) = Cy := by
  have hs : Function.Surjective (compFin F E v) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul x e =>
      refine ⟨GlobalTheory.LatVac.liftV v x ⊗ₜ e, ?_⟩
      simp [compFin, GlobalTheory.LatVac.evFin_liftV]
    | add x y hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, by rw [map_add (f := _), hp, hq]⟩
  choose f hf using hs
  exact ⟨Cy.map f, by ext i j; simp [hf]⟩

def lagSub {n d m : ℕ} (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : AddSubgroup (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) where
  carrier := GlobalTheory.InertVacLag.lagAt v C
  zero_mem' := ⟨fun u _ => smul_zero u, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, z, rfl⟩ ⟨hy, z', rfl⟩
    exact ⟨fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero], z + z', by rw [Matrix.add_mul]⟩
  neg_mem' := by
    rintro x ⟨hx, z, rfl⟩
    exact ⟨fun u hu => by rw [smul_neg, hx u hu, neg_zero], -z, by rw [Matrix.neg_mul]⟩

theorem acts_unique {κ : Type} [Fintype κ] (v : Pl (F := F)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (φ φ₁ φ₂ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v)) (h1 : Acts (evFin F v) T φ φ₁)
    (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have e := (h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ))
  funext y
  have hy := congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))
  simp only [tens] at hy
  have hev : (fun i => evFin F v (GlobalTheory.LatVac.liftV v (y i))) = y := funext fun i => GlobalTheory.LatVac.evFin_liftV v (y i)
  rw [hev] at hy
  have hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    have := (hR φ hφ).1 0 (fun i => GlobalTheory.LatVac.liftV v (y i)) (fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu)
    simpa using this
  rw [hRx] at hy
  exact mul_right_cancel₀ hR0 hy

theorem eq_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl (F := F)) (g u : W) (hg : At (evFin F v) g) (hu : At (evFin F v) u)
    (h : GlobalTheory.LatVac.locCo co v g = GlobalTheory.LatVac.locCo co v u) : g = u := by
  have hA : ∀ z : W, At (evFin F v) z → ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) := by
    intro z hz k
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have := congrArg (fun p => p.1 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
    · have := congrArg (fun p => p.2 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
  apply co.e.injective
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).1, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).1]
    exact congrArg _ (congrFun h1 k)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).2, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).2]
    exact congrArg _ (congrFun h2 k)

theorem exists_lagr_inv_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _
  obtain ⟨Cy, hCy⟩ := GlobalTheory.InertLagr.exists_lagr F E σ B a a' G X om om' hT v w hin
  obtain ⟨C, hC⟩ := exists_map_compFin (E := E) v Cy
  have hLag : GlobalTheory.InertVacLag.IsLagrAt σ G.W v C := by
    unfold GlobalTheory.InertVacLag.IsLagrAt; rw [hC]; exact hCy
  set co := G.M'.co with hco
  set Λ := (lagSub (n := a') v C).map (GlobalTheory.LatVac.locCo co v) with hΛ
  set Γ := (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo co v) with hΓ
  have hgood := hT.base.inert v w hin
  obtain ⟨hsb, hne, θ, hθ, hvac⟩ := hT.geo.hM'.vac v
  have hatL := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := hT.base.std.1.comp (GlobalTheory.VacAny.continuous_atPlace v)
  have hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) →
      x ∈ v.adicCompletionIntegers F := fun x hx => (hgood.2.2 x).1 hx
  have hiso : ∀ x ∈ Λ, ∀ x' ∈ Λ, x.1 ⬝ᵥ x'.2 - x'.1 ⬝ᵥ x.2 = 0 := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag (-1) u u' hu hu'
    change symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) u u' = 0 at h0
    rw [co.form] at h0
    have h1 := congrArg (evFin F v) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub] using h1
  have hOC := GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat v
  have hdual := GlobalTheory.LatVac.DualLoc.map_selfDual v co B.ψ (latAtV G.V' G.W v) hatL
    (GlobalTheory.T.inertPlace_tensorLattice_selfDual_supportedAt F E σ B a a' G X om om' hT v w hin)
  have heig0 : ∀ g ∈ latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v g) (G.M'.vac v) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) g g) • G.M'.vac v :=
    fun g hg => acts_unique v _ _ _ _ hsb (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v g (hatL g hg) _) (hvac g hg)
  have heig : ∀ γ ∈ Γ, ∃ c : ℂ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = c • G.M'.vac v := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, heig0 g hg⟩
  have hfix : ∀ γ ∈ Γ ⊓ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = G.M'.vac v := by
    rintro γ ⟨⟨g, hg, rfl⟩, ⟨u, hu, hgu⟩⟩
    have e : g = u := eq_of_locCo co v g u (hatL g hg) hu.1 hgu.symm
    subst e
    rw [heig0 g hg, GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag _ g g hu hu, mul_zero, AddChar.map_zero_eq_one, one_smul]
  obtain ⟨l, hl, hl0⟩ := GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness v (GlobalTheory.LatVac.psiAt B.ψ v) (Fin a' × Fin (a + a')) Λ Γ (G.M'.vac v) hψc hψ hiso
    hOC.1 hOC.2 hdual hsb hne heig hfix
  refine ⟨C, l, hLag, ?_, hl0⟩
  intro u hu φ hφ φ₁ _ hA
  have e := acts_unique v _ φ φ₁ _ hφ hA (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v u hu.1 φ)
  rw [e]
  exact hl _ ⟨u, hu, rfl⟩ φ hφ

end GlobalTheory.InertVacLagP

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuumStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  first | exact @GlobalTheory.InertVacLagP.exists_lagr_inv_vac | exact GlobalTheory.InertVacLagP.exists_lagr_inv_vac | (intros; apply GlobalTheory.InertVacLagP.exists_lagr_inv_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumNotMemAugmentationInertPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertVacLag

theorem vac_not_mem_augAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw hvT hmem
  obtain ⟨C, l, hC, hl, hne⟩ := GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum F E σ B a a' G X om om' hT v w hvw hvT
  have hle : augAt om' v ≤ LinearMap.ker l := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, ha, rfl⟩
    show φ₁ - φ ∈ LinearMap.ker l
    rw [LinearMap.mem_ker, map_sub,
      GlobalTheory.InertVacLag.inv_of_heisInv F E σ B a a' G X om om' hT v w hvw hvT _ C hC l hl g hg φ hφ φ₁ hφ₁ ha, sub_self]
  exact hne (hle hmem)

end GlobalTheory.InertVacLag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumNotMemAugmentationInertPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_not_mem_augmentation_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  first | exact @GlobalTheory.InertVacLag.vac_not_mem_augAt | exact GlobalTheory.InertVacLag.vac_not_mem_augAt | (intros; apply GlobalTheory.InertVacLag.vac_not_mem_augAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerVacuumScalarEqOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertScalarLeft

theorem scalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT k hk c hc
  by_contra hne
  have hSB := (hTr.geo.hM'.vac v).1
  apply GlobalTheory.T.weil_vacuum_not_mem_augmentation_inert_place F E σ B a a' G X om om' hTr v w hin hT
  have hmem : c • G.M'.vac v - G.M'.vac v ∈ augAt om' v :=
    Submodule.subset_span ⟨k, hk.1, _, hSB, _, Submodule.smul_mem _ c hSB, hc, rfl⟩
  have h1 : c - 1 ≠ 0 := sub_ne_zero.mpr hne
  have h2 : G.M'.vac v = (c - 1)⁻¹ • (c • G.M'.vac v - G.M'.vac v) := by
    rw [show c • G.M'.vac v - G.M'.vac v = (c - 1) • G.M'.vac v by rw [sub_smul, one_smul],
      smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ hmem

end GlobalTheory.InertScalarLeft
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerVacuumScalarEqOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeStabilizer_vacuumScalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @GlobalTheory.InertScalarLeft.scalar_eq_one | exact GlobalTheory.InertScalarLeft.scalar_eq_one | (intros; apply GlobalTheory.InertScalarLeft.scalar_eq_one <;> assumption)
end
