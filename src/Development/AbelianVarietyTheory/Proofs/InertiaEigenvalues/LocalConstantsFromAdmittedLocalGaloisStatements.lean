module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem localConstants_from_admitted_local_Galois_statements_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      LiftingTheory.aux₃ D HW F 10 23 32 32 :=
  fun _ _ _ D HW F Cm => Formalism.MainNotions.LiftingTheory.frobenius_lifting D HW F Cm (GlobalTheory.T.liftingTheorem_wachModuleLemma_hypotheses_admitted D HW F Cm).1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConstants_from_admitted_local_Galois_statements : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LiftingTheory.aux₃ D HW F 10 23 32 32 := by
  first | exact @GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt | exact GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt | (intros; apply GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (mem_fixed)

namespace GlobalTheory.LocGL

section FiniteGroup

variable {G V W X Y : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ W]

theorem charIdem_apply (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v =
      ((Module.finrank ℂ W : ℂ) / Fintype.card G) • ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v := by
  simp [charIdem, LinearMap.sum_apply]

theorem map_charIdem {σ : Representation ℂ G V} {σ' : Representation ℂ G X} (φ : σ.IntertwiningMap σ')
    (τ : Representation ℂ G W) (v : V) : φ (charIdem σ τ v) = charIdem σ' τ (φ v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [charIdem_apply, map_smul, map_sum, φ.isIntertwining]

theorem charIdem_apply_rep (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) (v : V) :
    charIdem σ τ (σ h v) = σ h (charIdem σ τ v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [charIdem_apply, map_smul, map_sum]
  congr 1
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun g => ?_).symm
  have e : LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) = LinearMap.trace ℂ W (τ g⁻¹) := by
    rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ by group]
    exact τ.char_conj g⁻¹ h
  show _ = LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) • σ (h * g * h⁻¹) (σ h v)
  rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

theorem commute_charIdem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) :
    Commute (charIdem σ τ) (σ h) := LinearMap.ext (charIdem_apply_rep σ τ h)

def coeffMap (σ : Representation ℂ G V) (τ : Representation ℂ G W) (ℓ : Module.Dual ℂ W) (v : V) :
    τ.IntertwiningMap σ where
  toLinearMap := ∑ g : G, (ℓ ∘ₗ τ g⁻¹).smulRight (σ g v)
  isIntertwining' h := LinearMap.ext fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul]
    refine (Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_).symm
    simp only [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem charIdem_mem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v ∈ isotypic σ τ := by
  classical
  let b := Module.finBasis ℂ W
  have key : ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v = ∑ i, coeffMap σ τ (b.coord i) v (b i) := by
    have : ∀ i, coeffMap σ τ (b.coord i) v (b i) = ∑ g : G, b.repr (τ g⁻¹ (b i)) i • σ g v := fun i => by
      show (∑ g : G, (b.coord i ∘ₗ τ g⁻¹).smulRight (σ g v)) (b i) = _
      simp [LinearMap.sum_apply]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  rw [charIdem_apply, key]
  exact (isotypic σ τ).toSubmodule.smul_mem _ (Submodule.sum_mem _ fun i _ => apply_mem_isotypic _ _)

theorem charIdem_self {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) : charIdem τ τ = 1 := by
  have := Model.nontrivial_of_isIrreducible hτ
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := τ)).2
    ⟨charIdem τ τ, fun g => commute_charIdem τ τ g⟩
  have h1 : charIdem τ τ = c • (1 : Module.End ℂ W) :=
    LinearMap.ext fun w => (congrArg (fun f : τ.IntertwiningMap τ => f w) hc).symm
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have ho := Representation.char_orthonormal τ τ
  rw [if_pos ⟨.refl _⟩, Nat.card_eq_fintype_card] at ho
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h2 : LinearMap.trace ℂ W (charIdem τ τ) = Module.finrank ℂ W := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [charIdem, map_smul, map_sum, smul_eq_mul]
    rw [div_eq_mul_inv, mul_assoc]
    refine (congrArg _ (Eq.trans ?_ ho)).trans (mul_one _)
    exact congrArg _ (Finset.sum_congr rfl fun g _ => mul_comm _ _)
  rw [h1, map_smul, LinearMap.trace_one, smul_eq_mul] at h2
  rw [h1, mul_right_cancel₀ hd (h2.trans (one_mul _).symm), one_smul]

theorem charIdem_of_mem {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) {v : V}
    (hv : v ∈ isotypic σ τ) : charIdem σ τ v = v := by
  refine Submodule.iSup_induction _ (motive := fun v => charIdem σ τ v = v) hv ?_ (map_zero _) fun x y hx hy => ?_
  · rintro f _ ⟨w, rfl⟩
    exact (map_charIdem f τ w).symm.trans (by rw [charIdem_self hτ]; rfl)
  · rw [map_add (f := _), hx, hy]

end FiniteGroup

section Compact

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G V} {σ : Representation ℂ G W} {H : Subgroup G}

theorem map_idem (hπ : IsSmooth π) (hσ : IsSmooth σ) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) (v : V) :
    f (idem hπ hH v) = idem hσ hH (f v) := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  rw [idem_eq_cosetSum hπ hH U hU, idem_eq_cosetSum hσ hH U fun u hu => by rw [← f.isIntertwining, hU u hu]]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, f.isIntertwining]

theorem map_idem_of_mem (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : f (idem hπ hH v) = f v := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [idem_eq_cosetSum hπ hH U hU]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, f.isIntertwining]
  rw [Finset.sum_congr rfl fun q _ => mem_fixed.1 hv _ (q.out : H).2, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem exists_mem_fixed_map_eq (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : ∃ u ∈ fixed π H, f u = f v :=
  ⟨_, idem_mem hπ hH v, map_idem_of_mem hπ hH f hv⟩

theorem map_fixed_of_surjective (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) {f : π.IntertwiningMap σ}
    (hf : Function.Surjective f) : (fixed π H).map f.toLinearMap = fixed σ H := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact mem_fixed.2 fun u hu => by rw [f.toLinearMap_apply, ← f.isIntertwining, mem_fixed.1 hv u hu]
  · obtain ⟨v, rfl⟩ := hf w
    exact exists_mem_fixed_map_eq hπ hH f hw

end Compact

section LevelZero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W}
  {ρ : Representation ℂ (GL n k) X}

theorem levelZeroMap_injective {f : π.IntertwiningMap σ} (hf : Function.Injective f) :
    Function.Injective (levelZeroMap f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem levelZeroMap_surjective (hπ : IsSmooth π) {f : π.IntertwiningMap σ} (hf : Function.Surjective f) :
    Function.Surjective (levelZeroMap f) := by
  rintro ⟨x, hx⟩
  obtain ⟨v, rfl⟩ := hf x
  obtain ⟨u, hu, h⟩ := exists_mem_fixed_map_eq hπ (levelPre_bot (k := k) (n := n) ▸ isCompact_levelPre ⊥) f hx
  exact ⟨⟨u, hu⟩, Subtype.ext h⟩

end LevelZero

end GlobalTheory.LocGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infGL_mem_UA {n : ℕ} (y : GL (Fin n) (Cinf E)) (hy : y.valᴴ * y.val = 1) : infGL E n y ∈ UA E n := by
  change cT (conjAd E) (infGL E n y).val * 1 * (infGL E n y).val = 1
  have h1 : (infGL E n y).val.map (pInf E) = y.val := congrArg Units.val (pInf_infGL y)
  have h2 : (infGL E n y).val.map (pFin E) = 1 := congrArg Units.val (pFin_infGL y)
  have h3 : (cT (conjAd E) (infGL E n y).val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have h4 : (cT (conjAd E) (infGL E n y).val).map (pFin E) = 1 := by
    ext1 i j
    change conjFin (IsCMField.complexConj E).toRingEquiv (((infGL E n y).val.map (pFin E)) j i) = _
    rw [h2]
    simp only [Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h5 := congrArg₂ (· * ·) h3 h1
  have h6 := congrArg₂ (· * ·) h4 h2
  simp only [← Matrix.map_mul, hy, mul_one] at h5 h6
  rw [mul_one]
  ext1 i j
  refine ad_ext ((congrFun₂ h5 i j).trans ?_) ((congrFun₂ h6 i j).trans ?_) <;>
  · simp only [Matrix.one_apply]
    split_ifs <;> simp


end GlobalTheory.UnitaryBC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph
open MeasureTheory

namespace GlobalTheory.SplitWeil

theorem nabs_map_of_homeomorph : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → ∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x := by
  intro k k' _ _ _ _ _ _ _ _ i hi hi' x
  haveI : SecondCountableTopology k := (Model.secondCountable_and_t2_local_field (k := k)).1
  haveI : T2Space k := (Model.secondCountable_and_t2_local_field (k := k)).2
  haveI : SecondCountableTopology k' := (Model.secondCountable_and_t2_local_field (k := k')).1
  haveI : T2Space k' := (Model.secondCountable_and_t2_local_field (k := k')).2
  let e : k ≃ₜ+ k' :=
    { i.toAddEquiv with
      continuous_toFun := hi
      continuous_invFun := hi' }
  unfold nabs
  congr 1
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e x (Units.map i.toRingHom.toMonoidHom x) (fun y => by
    change i ((x : k) * y) = i x * i y
    exact map_mul i _ _)

end GlobalTheory.SplitWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorphStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedAbsValueLocalFieldUnit_map_homeomorph : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → ∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x := by
  first | exact @GlobalTheory.SplitWeil.nabs_map_of_homeomorph | exact GlobalTheory.SplitWeil.nabs_map_of_homeomorph | (intros; apply GlobalTheory.SplitWeil.nabs_map_of_homeomorph <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

def yInf (g : GA E (m + 1)) : Fin (m + 1) → Cinf E := fun i => pInf E (GlobalTheory.ZEul.lastRow g i)

def yFin (g : GA E (m + 1)) : Fin (m + 1) → Af E := fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)

def sqrtC (Φ : (Fin (m + 1) → Cinf E) → ℂ) (u : Fin (m + 1) → Cinf E) : ℂ := (Real.sqrt (Φ u).re : ℂ)

def fT (φ : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (g : GA E (m + 1)) : ℂ :=
  φ (g * infGL E (m + 1) (secInv (yInf g))) * sqrtC Φ (yInf g)

def wt (N : ℕ) (x : ℝ) (g : GA E (m + 1)) : ℝ≥0 := Real.toNNReal ((indN N (yFin g)).re * detPow E (m + 1) x g)

theorem yInf_of_lastRow {g g' : GA E (m + 1)} (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g) : yInf g' = yInf g := by
  funext i; exact congrArg (fun r => pInf E (r i)) h

theorem yFin_of_lastRow {g g' : GA E (m + 1)} (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g) : yFin g' = yFin g := by
  funext i; exact congrArg (fun r => GlobalTheory.RSJ.pFin E (r i)) h

theorem fT_of_lastRow {φ : GA E (m + 1) → ℂ} {Φ : (Fin (m + 1) → Cinf E) → ℂ} {g g' : GA E (m + 1)}
    (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g) :
    fT φ Φ g' = φ (g' * infGL E (m + 1) (secInv (yInf g))) * sqrtC Φ (yInf g) := by
  rw [fT, yInf_of_lastRow h]

theorem wt_of_lastRow_of_detPow {N : ℕ} {x : ℝ} {g g' : GA E (m + 1)} (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g)
    (hd : detPow E (m + 1) x g' = detPow E (m + 1) x g) : wt N x g' = wt N x g := by
  rw [wt, wt, yFin_of_lastRow h, hd]

end GlobalTheory.ZUnf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.LocGL

section Rad

variable {R S : Type} [CommRing R] [CommRing S] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem map_mem_unipRad_of_ringHom (f : R →+* S) {e : (Σ a, m a) ≃ n} {g : GL n R} (hg : g ∈ unipRad R e) :
    GeneralLinearGroup.map f g ∈ unipRad S e := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hg
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · show f ((g : Matrix n n R) i j) = 0
    rw [mem_parab.1 h1 i j hij, map_zero]
  · show f ((g : Matrix n n R) _ _) = _
    rw [h2 a i j]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end Rad

theorem isCuspidal_comp_generalLinearGroupMap {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k') (hi : Continuous i.symm) {n : Type} [Fintype n]
    [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (h : IsCuspidal π) : IsCuspidal (π.comp (GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  set M := GeneralLinearGroup.map (n := n) i.symm.toRingHom with hM
  have hc : Continuous M :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  refine ⟨fun v => (h.1 v).preimage hc, fun s d e he => ?_⟩
  have hmem : ∀ u ∈ unipRad k' e, M u ∈ unipRad k e := fun u hu => map_mem_unipRad_of_ringHom _ hu
  have hsurj : ∀ w ∈ unipRad k e, ∃ u ∈ unipRad k' e, M u = w := fun w hw =>
    ⟨GeneralLinearGroup.map i.toRingHom w, map_mem_unipRad_of_ringHom _ hw,
      Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩
  have hinj : Function.Injective M := fun x y hxy => Units.ext (Matrix.ext fun a b =>
    i.symm.injective (congrArg (fun g : GL n k => (g : Matrix n n k) a b) hxy))
  have hne : unipRad k e ≠ ⊥ := fun hb => he ((Subgroup.eq_bot_iff_forall _).2 fun u hu =>
    hinj ((((Subgroup.eq_bot_iff_forall _).1 hb) _ (hmem u hu)).trans (map_one M).symm))
  have h1 : twKer (π.comp M) (unipRad k' e) 1 = twKer π (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨⟨M u, hmem u u.2⟩, v, by simp⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u', hu', hu⟩ := hsurj u u.2
      exact ⟨⟨u', hu'⟩, v, by simp [hu]⟩
  exact Submodule.Quotient.subsingleton_iff.2 (h1 ▸ Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne))

end GlobalTheory.LocGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldEStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSupercuspidal_comp_generalLinearGroupMapOfFieldEquiv : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i.symm → ∀ {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), GlobalTheory.SmGL.IsCuspidal π → GlobalTheory.SmGL.IsCuspidal (π.comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  first | exact @GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | exact GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | (intros; apply GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.LocGL

theorem exists_linearEquiv_of_subsingleton {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  have hst : ∀ (U : Submodule ℂ V) (g : G) ⦃v : V⦄, v ∈ U → π g v ∈ U := fun U g v hv => by
    rw [Subsingleton.elim g 1, map_one]
    exact hv
  have := hi
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.ext
    ext w
    rw [h w]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  have htop : Submodule.span ℂ {v} = ⊤ := by
    rcases eq_bot_or_eq_top (⟨Submodule.span ℂ {v}, hst _⟩ : Subrepresentation π) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp (congrArg Subrepresentation.toSubmodule h)) hv
    · exact congrArg Subrepresentation.toSubmodule h
  exact ⟨((LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ htop)).symm⟩

theorem exists_equiv_piTensor_two {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (f : X 1 ≃ₗ[ℂ] ℂ) : ∃ (b : ∀ a, X a) (L : X 0 ≃ₗ[ℂ] PiTensorProduct ℂ X),
      ∀ v, L v = PiTensorProduct.tprod ℂ (Function.update b 0 v) := by
  classical
  let b : ∀ a, X a := Pi.single 1 (f.symm 1)
  have hb : b 1 = f.symm 1 := Pi.single_eq_same _ _
  let μ : MultilinearMap (RingHom.id ℂ) X (X 0) :=
    { toFun := fun x => f (x 1) • x 0
      map_update_add' := by
        intro _ x i p q
        fin_cases i
        · simp only [Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true,
            Function.update_of_ne, smul_add]
        · simp only [Fin.mk_one, Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
            Function.update_of_ne, map_add, add_smul]
      map_update_smul' := by
        intro _ x i c p
        fin_cases i
        · simp only [Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true,
            Function.update_of_ne, RingHom.id_apply, smul_comm (f (x 1)) c]
        · simp only [Fin.mk_one, Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
            Function.update_of_ne, map_smul, smul_eq_mul, mul_smul, RingHom.id_apply] }
  have hμ : ∀ x, μ x = f (x 1) • x 0 := fun _ => rfl
  let φ : X 0 →ₗ[ℂ] PiTensorProduct ℂ X := (PiTensorProduct.tprod ℂ).toLinearMap b 0
  have hφ : ∀ v, φ v = PiTensorProduct.tprod ℂ (Function.update b 0 v) := fun _ => rfl
  refine ⟨b, LinearEquiv.ofLinearMap φ (PiTensorProduct.lift μ) ?_ ?_, hφ⟩
  · apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.lift.tprod, hμ, hφ, LinearMap.id_coe, id_eq]
    have hx : x = Function.update (Function.update b 0 (x 0)) 1
        (f (x 1) • Function.update b 0 (x 0) 1) := by
      funext a
      fin_cases a
      · simp
      · simp only [Fin.mk_one, Function.update_self]
        rw [Function.update_of_ne (by decide), hb, ← map_smul, smul_eq_mul, mul_one,
          LinearEquiv.symm_apply_apply]
    conv_rhs => rw [hx]
    rw [MultilinearMap.map_update_smul (PiTensorProduct.tprod ℂ) b 0,
      MultilinearMap.map_update_smul (PiTensorProduct.tprod ℂ) (Function.update b 0 (x 0)) 1,
      Function.update_eq_self]
  · apply LinearMap.ext
    intro v
    simp only [LinearMap.coe_comp, Function.comp_apply, hφ, PiTensorProduct.lift.tprod, hμ,
      LinearMap.id_coe, id_eq, Function.update_self]
    rw [Function.update_of_ne (by decide), hb, LinearEquiv.apply_symm_apply, one_smul]

private theorem mem_parab_of_isEmpty_second_block {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [IsEmpty (m 1)] (e : (Σ a, m a) ≃ m 0) (g : GL (m 0) k) : g ∈ parab k e := by
  have hb : ∀ x : m 0, blk e x = 0 := by
    intro x
    unfold blk
    generalize e.symm x = s
    obtain ⟨a, y⟩ := s
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · rfl
    · exact isEmptyElim y
  rw [mem_parab]
  intro i j hij
  rw [hb i, hb j] at hij
  exact absurd hij (lt_irrefl _)

private theorem leviProj_zero_eq_coe {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (e : (Σ a, m a) ≃ m 0) (he : ∀ i, e ⟨0, i⟩ = i) (p : parab k e) :
    leviProj k e p 0 = (p : GL (m 0) k) :=
  Units.ext (Matrix.ext fun i j => by rw [leviProj_apply, he, he])

private theorem deltaHalf_eq_one_of_isEmpty_second_block {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [IsEmpty (m 1)] (g : Levi k m) : deltaHalf k m g = 1 := by
  have : Subsingleton (GL (m 1) k) := ⟨fun a b => Units.ext (Matrix.ext fun i => isEmptyElim i)⟩
  have h0 : modExp m 0 = 0 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two, Fintype.card_eq_zero]
  have h1 : g 1 = 1 := Subsingleton.elim _ _
  rw [deltaHalf_apply, Fin.prod_univ_two, h0, h1, map_one, map_one, mul_one]
  simp [absPow_zero]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_multiProd_empty {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [IsEmpty (m 1)] {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {π : ∀ a, Representation ℂ (GL (m a) k) (X a)} (hπ : IsSmooth (π 0)) (hi : (π 1).IsIrreducible)
    (e : (Σ a, m a) ≃ m 0) (he : ∀ i, e ⟨0, i⟩ = i) : Nonempty ((π 0).Equiv (multiProd e π)) := by
  have : Subsingleton (GL (m 1) k) := ⟨fun a b => Units.ext (Matrix.ext fun i => isEmptyElim i)⟩
  obtain ⟨f₁⟩ := exists_linearEquiv_of_subsingleton hi
  obtain ⟨b, L, hL⟩ := exists_equiv_piTensor_two f₁
  have hσ : ∀ (p : parab k e) (u : X 0),
      (GlobalTheory.SmGL.twist (piTensor π) (deltaHalf k m)) (leviProj k e p) (L u) = L (π 0 (p : GL (m 0) k) u) := by
    intro p u
    rw [twist_apply, deltaHalf_eq_one_of_isEmpty_second_block, Units.val_one, one_smul, hL, hL, piTensor_tprod]
    congr 1
    funext a
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · rw [Function.update_self, Function.update_self, leviProj_zero_eq_coe e he]
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Subsingleton.elim (leviProj k e p 1) 1, map_one, Module.End.one_apply]
  have hval : ∀ (f : IndSp e (piTensor π)) (g : GL (m 0) k),
      f.1.1 g = L (π 0 g (L.symm (f.1.1 1))) := by
    intro f g
    have h := (f.1.2 : ∀ (h : parab k e) (x : GL (m 0) k), f.1.1 (h * x) = _) ⟨g, mem_parab_of_isEmpty_second_block e g⟩ 1
    rw [mul_one] at h
    have h' := hσ ⟨g, mem_parab_of_isEmpty_second_block e g⟩ (L.symm (f.1.1 1))
    rw [LinearEquiv.apply_symm_apply] at h'
    rw [h]
    exact h'
  let G : IndSp e (piTensor π) →ₗ[ℂ] X 0 :=
    L.symm.toLinearMap ∘ₗ LinearMap.proj 1 ∘ₗ (indSpace _ _).subtype ∘ₗ (smoothPart _).subtype
  have hG : ∀ f, G f = L.symm (f.1.1 1) := fun _ => rfl
  have hinj : Function.Injective G := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    rw [hG] at hf
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [hval, hf, map_zero, map_zero]
    rfl
  have hsurj : Function.Surjective G := by
    intro v
    let F : GL (m 0) k → PiTensorProduct ℂ X := fun g => L (π 0 g v)
    have hF : F ∈ indSpace (parab k e) ((GlobalTheory.SmGL.twist (piTensor π) (deltaHalf k m)).comp (leviProj k e)) := by
      intro p g
      show L (π 0 (p * g) v) = _
      rw [map_mul, Module.End.mul_apply, MonoidHom.comp_apply, hσ]
    have hS : (⟨F, hF⟩ : indSpace _ _) ∈ smoothPart (ind (parab k e)
        ((GlobalTheory.SmGL.twist (piTensor π) (deltaHalf k m)).comp (leviProj k e))) := by
      have hset : {g' : GL (m 0) k | ind (parab k e) ((GlobalTheory.SmGL.twist (piTensor π) (deltaHalf k m)).comp
          (leviProj k e)) g' ⟨F, hF⟩ = ⟨F, hF⟩} = {g' | π 0 g' v = v} := by
        ext g'
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          have h1 := congrArg (fun φ : indSpace _ _ => φ.1 1) h
          have h2 : L (π 0 (1 * g') v) = L (π 0 1 v) := h1
          rw [one_mul, map_one, Module.End.one_apply] at h2
          exact L.injective h2
        · intro h
          apply Subtype.ext
          funext x
          show L (π 0 (x * g') v) = L (π 0 x v)
          rw [map_mul, Module.End.mul_apply, h]
      have hopen : IsOpen {g' : GL (m 0) k | ind (parab k e) ((GlobalTheory.SmGL.twist (piTensor π) (deltaHalf k m)).comp
          (leviProj k e)) g' ⟨F, hF⟩ = ⟨F, hF⟩} := by
        rw [hset]
        exact hπ v
      exact hopen
    refine ⟨⟨⟨F, hF⟩, hS⟩, ?_⟩
    rw [hG]
    show L.symm (L (π 0 1 v)) = v
    rw [LinearEquiv.symm_apply_apply, map_one, Module.End.one_apply]
  refine ⟨(Representation.Equiv.mk (LinearEquiv.ofBijective G ⟨hinj, hsurj⟩) fun g => ?_).symm⟩
  apply LinearMap.ext
  intro f
  show G (multiProd e π g f) = π 0 g (G f)
  rw [hG, hG]
  rw [show ((multiProd e π g f).1.1 1) = f.1.1 g from by
    unfold multiProd
    rw [parInd_apply, one_mul]]
  rw [hval, LinearEquiv.symm_apply_apply]

theorem nonempty_equiv_prodIrr_two_zero (y : Fin 2 → IrrGL (k := k)) (hz : (y 1).1 = 0) (hd : ∑ a, (y a).1 = (y 0).1) :
    Nonempty ((y 0).rep.Equiv (prodIrr y hd)) := by
  have : IsEmpty (Fin (y 1).1) := by rw [hz]; infer_instance
  refine nonempty_equiv_multiProd_empty (m := fun a => Fin (y a).1) (X := fun a => (y a).2.rep.V)
    (π := fun a => (y a).rep) (y 0).2.rep.smooth (y 1).2.rep.irr _ fun i => ?_
  apply Fin.ext
  rw [stdBlocks_val]
  simp

theorem nonempty_equiv_prodIrr_pair_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x z : IrrGL (k := k)) (hz : z.1 = 0) (hd : ∑ a, (![x, z] a).1 = x.1) :
    Nonempty (x.rep.Equiv (prodIrr ![x, z] hd)) := nonempty_equiv_prodIrr_two_zero ![x, z] hz hd

end GlobalTheory.LocGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZeroStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_equiv_prodChosenIrrGL_pair_degreeZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x z : IrrGL (k := k)) (hz : z.1 = 0) (hd : ∑ a, (![x, z] a).1 = x.1), Nonempty (x.rep.Equiv (prodIrr ![x, z] hd)) := by
  first | exact @GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero | exact GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero | (intros; apply GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricPropertiesAllOfBound
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricDistribution

namespace GlobalTheory.ToricAssembly

theorem toricSumFormula : ToricSumFormula :=
  GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors exists_isHeckeL_of_hasInf

theorem not_isNormPow {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {χ : HChar E} (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ) :
    ¬ ∃ t : ℝ, GlobalTheory.HeckeOne.IsNormPow χ t := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hb.2.1
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, fun h => hb.1 (le_bot_iff.1 (h ▸ hle))⟩
  have hv : v.asIdeal ∣ 𝔣 := Ideal.dvd_iff_le.2 hle
  obtain ⟨P, -, -, hP, -⟩ := (hb.2.2 v hv).1
  exact GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt
    (((hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)).not_unrAt ((multiplicity_ne_zero (Ideal.finiteMultiplicity hM.ne_top hb.1)).2 hv))

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem qOk_empty (i : X.Tw) : BlochKatoReduction.Gen.QOk X i ∅ :=
  ⟨fun _ h => absurd h (Finset.notMem_empty _), Finset.disjoint_empty_left _, fun _ h => absurd h (Finset.notMem_empty _)⟩

theorem sum_ne_zero_at (hL : ToricSumFormula) {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {s : ℕ}
    (ht : IsToricEltAt X i ι lam s) : ∑ δ, X.th i ∅ lam δ ≠ 0 := by
  classical
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, -, hu, hth⟩ := ht
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth ∅ (qOk_empty i)
  have he : belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))) = ∅ := Finset.image_empty _
  obtain ⟨hφ, -, hs, -, hb, hχ⟩ := hD
  have hn := not_isNormPow hb hχ
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn
  have h0 : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 D.host.E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := hL _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ host_unramFin hs hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ
    (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one, ← he] at t1
  have := Fintype.ofFinite (PicO (condQ 𝔣 (belowSet ∅)))
  have e : Λ s = ∑ q, T q :=
    t1.unique ((isToricSum_iff _ _ _ _ _ _).2 ⟨hfin, T, hT, (finsum_eq_sum_of_fintype _).symm⟩)
  intro hz
  have h1 := congrArg (algebraMap (FractionRing (X.O i)) (Kbar X i)) hz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Finset.sum_congr rfl fun δ _ => hδ δ, ← Finset.mul_sum, ← map_sum] at h1
  refine mul_ne_zero hu ((map_ne_zero ι).2 ?_) h1
  rw [e, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹)] at h0
  convert h0 using 2 with δ
  rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset]

theorem gen_sum_ne_zero (hL : ToricSumFormula) (ht : IsToricElt X) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (lam : X.abelian₂ i)
    (hs : ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s) : ∑ δ, X.th i ∅ lam δ ≠ 0 := by
  obtain ⟨s, hs⟩ := hs
  obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)
  obtain ⟨ι, -, hι⟩ := ht i hi
  exact sum_ne_zero_at hL (hι lam s hs)

theorem gen_toric_properties (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hL : ToricSumFormula) (hB : ClassTermBound)
    (ht : IsToricElt X) :
    ∃ N0 : X.Tw → ℕ, BlochKatoReduction.Gen.adm9 X N0 ∧ BlochKatoReduction.Gen.adm10 X ∧
      ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, (∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s) → ∑ δ, X.th i ∅ lam δ ≠ 0 := by
  obtain ⟨N0, h⟩ := exists_gen_bound X hB ht
  exact ⟨N0, h, gen_relation hA hL ht, gen_sum_ne_zero hL ht⟩

end Record

theorem toric_properties_of_bound (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hB : ClassTermBound) (D : D7)
    (ht : IsToricElt D.ntw) :
    ∃ N0 : D.ntw.Tw → ℕ, BlochKatoReduction.adm9 D N0 ∧ BlochKatoReduction.adm10 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → ∀ lam : D.ntw.abelian₂ i, (∃ s : ℤ, BlochKatoReduction.Gen.SOk D.ntw i lam s) → ∑ δ, D.ntw.th i ∅ lam δ ≠ 0 :=
  gen_toric_properties hA toricSumFormula hB ht

theorem toric_properties (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hB : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator) (D : D7)
    (ht : IsToricElt D.ntw) :
    ∃ N0 : D.ntw.Tw → ℕ, BlochKatoReduction.adm9 D N0 ∧ BlochKatoReduction.adm10 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → ∀ lam : D.ntw.abelian₂ i, (∃ s : ℤ, BlochKatoReduction.Gen.SOk D.ntw i lam s) → ∑ δ, D.ntw.th i ∅ lam δ ≠ 0 :=
  toric_properties_of_bound hA (GlobalTheory.ToricDenomBridge.classTermBound_of_toricDenominator hB) D ht

end GlobalTheory.ToricAssembly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionCompGeneralLinearGroupMapOfFie
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionCompGeneralLinearGroupMapOfFie
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil Matrix

namespace GlobalTheory.IndField

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

section Gen

variable {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁] [IsNonarchimedeanLocalField K₁]
  [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂] [IsNonarchimedeanLocalField K₂]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullFun (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi K₁ m) W}
    {ρ₂ : Representation ℂ (Levi K₂ m) W}
    (s : GL n K₂ →* GL n K₁) (hs : Continuous s) (t : Levi K₂ m →* Levi K₁ m)
    (hP : ∀ p : parab K₂ e, s p ∈ parab K₁ e)
    (hL : ∀ p : parab K₂ e, leviProj K₁ e ⟨s p, hP p⟩ = t (leviProj K₂ e p))
    (hρ : ∀ L, ρ₂ L = ρ₁ (t L)) (hδ : ∀ L, deltaHalf K₁ m (t L) = deltaHalf K₂ m L) :
    IndSp e ρ₁ →ₗ[ℂ] IndSp e ρ₂ where
  toFun f := ⟨⟨fun x => f.1.1 (s x), fun p g => by
      show f.1.1 (s ((p : GL n K₂) * g)) =
        (deltaHalf K₂ m (leviProj K₂ e p) : ℂ) • ρ₂ (leviProj K₂ e p) (f.1.1 (s g))
      rw [map_mul, parInd_law e ρ₁ f ⟨s p, hP p⟩ (s g), hL, hδ, hρ]⟩, by
      apply mem_smoothPart_of_nhds
      have h1 : s ⁻¹' {g | ind (parab K₁ e) ((GlobalTheory.SmGL.twist ρ₁ (deltaHalf K₁ m)).comp (leviProj K₁ e)) g f.1 = f.1}
          ∈ nhds (1 : GL n K₂) :=
        (f.2.preimage hs).mem_nhds (by simp)
      refine Filter.mem_of_superset h1 fun x hx => ?_
      refine Subtype.ext (funext fun y => ?_)
      show f.1.1 (s (y * x)) = f.1.1 (s y)
      rw [map_mul]
      exact congrArg (fun v : indSpace (parab K₁ e) ((GlobalTheory.SmGL.twist ρ₁ (deltaHalf K₁ m)).comp (leviProj K₁ e)) =>
        (v : GL n K₁ → W) (s y)) hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Gen

section Gen2

variable {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁] [IsNonarchimedeanLocalField K₁]
  [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂] [IsNonarchimedeanLocalField K₂]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullMap (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi K₁ m) W}
    {ρ₂ : Representation ℂ (Levi K₂ m) W}
    (s : GL n K₂ →* GL n K₁) (hs : Continuous s) (t : Levi K₂ m →* Levi K₁ m)
    (hP : ∀ p : parab K₂ e, s p ∈ parab K₁ e)
    (hL : ∀ p : parab K₂ e, leviProj K₁ e ⟨s p, hP p⟩ = t (leviProj K₂ e p))
    (hρ : ∀ L, ρ₂ L = ρ₁ (t L)) (hδ : ∀ L, deltaHalf K₁ m (t L) = deltaHalf K₂ m L) :
    Representation.IntertwiningMap ((parInd e ρ₁).comp s) (parInd e ρ₂) :=
  ⟨pullFun e s hs t hP hL hρ hδ, fun g => LinearMap.ext fun f =>
    Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (s x * s g) = f.1.1 (s (x * g))
      rw [map_mul]))⟩

end Gen2

section Map

variable {R S : Type} [CommRing R] [CommRing S]

def blockMap (φ : R →+* S) : Levi R m →* Levi S m :=
  MonoidHom.pi fun a => (GeneralLinearGroup.map φ).comp (Pi.evalMonoidHom (fun a => GL (m a) R) a)

@[simp] theorem blockMap_apply (φ : R →+* S) (L : Levi R m) (a : α) :
    blockMap φ L a = GeneralLinearGroup.map φ (L a) := rfl


omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem map_mem_parab (e : (Σ a, m a) ≃ n) (φ : R →+* S) (p : parab R e) :
    GeneralLinearGroup.map φ (p : GL n R) ∈ parab S e :=
  mem_parab.2 fun i j h => by
    change φ (((p : GL n R) : Matrix n n R) i j) = 0
    rw [mem_parab.1 p.2 i j h, map_zero]

theorem leviProj_map (e : (Σ a, m a) ≃ n) (φ : R →+* S) (p : parab R e) :
    leviProj S e ⟨GeneralLinearGroup.map φ (p : GL n R), map_mem_parab e φ p⟩ =
      blockMap φ (leviProj R e p) :=
  funext fun _ => Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem continuous_glMap [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
    (φ : R →+* S) (hφ : Continuous φ) : Continuous (GeneralLinearGroup.map (n := n) φ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_map hφ : Continuous fun g : GL n R => (g : Matrix n n R).map φ)
  · have : (fun g : GL n R => (((GeneralLinearGroup.map φ g)⁻¹ : GL n S) : Matrix n n S)) =
        fun g => ((g⁻¹ : GL n R) : Matrix n n R).map φ := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map hφ

end Map

theorem deltaHalf_blockMap {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [IsNonarchimedeanLocalField K₁] [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂]
    [IsNonarchimedeanLocalField K₂] (φ : K₂ →+* K₁)
    (hn : ∀ y : K₂ˣ, nabs K₁ (Units.map φ.toMonoidHom y) = nabs K₂ y) (L : Levi K₂ m) :
    deltaHalf K₁ m (blockMap φ L) = deltaHalf K₂ m L := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => Units.ext ?_
  rw [val_absPow, val_absPow, blockMap_apply, GeneralLinearGroup.map_det]
  exact congrArg (fun r : ℝ => ((r : ℂ)) ^ _) (hn _)

theorem multiProd_comp_glMap : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → (∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x) → ∀ {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.multiProd e σ).comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) (GlobalTheory.SmGL.multiProd e fun a => (σ a).comp (Matrix.GeneralLinearGroup.map (n := m a) i.symm.toRingHom))) := by
  intro k k' _ _ _ _ _ _ _ _ i hi hi' hn α n m _ _ _ _ _ _ e X _ _ σ
  have hn' : ∀ y : k'ˣ, nabs k (Units.map i.symm.toRingHom.toMonoidHom y) = nabs k' y := fun y => by
    have h := hn (Units.map i.symm.toRingHom.toMonoidHom y)
    rw [show Units.map i.toRingHom.toMonoidHom (Units.map i.symm.toRingHom.toMonoidHom y) = y from
      Units.ext (by simp)] at h
    exact h.symm
  let Φ := pullMap e (ρ₁ := piTensor σ) (ρ₂ := piTensor fun a => (σ a).comp
      (GeneralLinearGroup.map (n := m a) i.symm.toRingHom))
    (GeneralLinearGroup.map i.symm.toRingHom) (continuous_glMap _ hi')
    (blockMap i.symm.toRingHom) (fun p => map_mem_parab e _ p) (fun p => leviProj_map e _ p)
    (fun _ => rfl) (fun L => deltaHalf_blockMap _ hn' L)
  let Ψ := pullFun e (ρ₁ := piTensor fun a => (σ a).comp
      (GeneralLinearGroup.map (n := m a) i.symm.toRingHom)) (ρ₂ := piTensor σ)
    (GeneralLinearGroup.map i.toRingHom) (continuous_glMap _ hi)
    (blockMap i.toRingHom) (fun p => map_mem_parab e _ p) (fun p => leviProj_map e _ p)
    (fun L => by
      show piTensor σ L = piTensor σ (fun a => GeneralLinearGroup.map i.symm.toRingHom
        (GeneralLinearGroup.map i.toRingHom (L a)))
      congr 1
      funext a
      ext
      simp) (fun L => deltaHalf_blockMap _ hn L)
  refine ⟨GlobalTheory.LocGL.equivOfBijective Φ (Function.bijective_iff_has_inverse.2 ⟨Ψ, fun f => ?_, fun f => ?_⟩)⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom x)) = f.1.1 x
    rw [show GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom x) = x from
      Matrix.GeneralLinearGroup.ext fun _ _ => by simp]
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom x)) = f.1.1 x
    rw [show GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom x) = x from
      Matrix.GeneralLinearGroup.ext fun _ _ => by simp]

end GlobalTheory.IndField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionCompGeneralLinearGroupMapOfFieStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInduction_comp_generalLinearGroupMapOfFieldEquiv : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → (∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x) → ∀ {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.multiProd e σ).comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) (GlobalTheory.SmGL.multiProd e fun a => (σ a).comp (Matrix.GeneralLinearGroup.map (n := m a) i.symm.toRingHom))) := by
  first | exact @GlobalTheory.IndField.multiProd_comp_glMap | exact GlobalTheory.IndField.multiProd_comp_glMap | (intros; apply GlobalTheory.IndField.multiProd_comp_glMap <;> assumption)
end
end
