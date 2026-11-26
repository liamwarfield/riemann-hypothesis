module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealisedE

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PetIntOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem petInt_of_cuspRapidDecay (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) : PetInt D :=
  fun _ hθ _ μ 𝓕 hq _ _ hψ hφ =>
    GlobalTheory.CuspDecay.integrableOn_star_mul hP GlobalTheory.Mem.VolFin.finVol hθ μ 𝓕 hq.1 hq.2 hψ hφ.1 hφ.2

end GlobalTheory.Mem.Th
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftAutEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem liftAutEq : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAutEq D := by
  intro hP D θ hθ ψ hψ V W χ χ' ha om hom μ 𝓕 hq Φ F hF
  obtain ⟨omO, H, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha hom
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  have hf := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
  simp only [hE] at hf
  have e' : ∀ g h, (om (g, h) Φ).1 0 = thKer ψ V W omO ⟨fun x => Φ.1 (toTWsmall V W x), hf⟩ g h := fun g h => by
    have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm
  simp only [e']
  exact (isKerSys_thKer hθ hψ (GlobalTheory.Ker.isWeak_of_datum H) H.om_cont).lift hP hθ hq hF _

end GlobalTheory.Mem.Lift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqualRankSplittingCharsAdmissibleMulRight
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilEqRank

variable {D : D7}

theorem equalRankSplittingCharsAdmissible_mul_right {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W χ (χ' * ν) :=
  ⟨h.1, h.2.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ' ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.2.1, resEta_mul h.2.2.2.2 h0⟩

theorem equalRankSplittingCharsAdmissible_mul_left {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W (χ * ν) χ' :=
  ⟨h.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.1, resEta_mul h.2.2.2.1 h0, h.2.2.2.2⟩

theorem exists_weilFun_eqRank : ∀ D : D7, WeilEx D → WeilOnEqEx D → WeilTwEq D → ∀ ψ, IsStdChar D ψ (-1) →
    ∃ Wf : WeilFun D ψ, Wf.EqRank := by
  classical
  intro D h1 h2 h3 ψ hψ
  obtain ⟨W₀⟩ := h1 ψ hψ
  have key : ∀ (V W : HSp D) (χ χ' : IdC D), ∃ om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W),
      (V.rank ≠ W.rank → om = W₀.om V W χ χ') ∧ (AdmE V W χ χ' → IsWeilOn ψ V W χ χ' om) := fun V W χ χ' => by
    by_cases h : AdmE V W χ χ'
    · obtain ⟨om, hom⟩ := h2 ψ hψ V W χ χ' h
      exact ⟨om, fun hne => absurd h.1 hne, fun _ => hom⟩
    · exact ⟨W₀.om V W χ χ', fun _ => rfl, fun k => absurd k h⟩
  choose om hne heq using key
  refine ⟨⟨om, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_⟩, heq, fun V W χ χ' ν ha hν h0 => ?_, fun V W χ χ' ν ha hν h0 => ?_⟩
  · rw [hne V W χ χ' ha.1]; exact W₀.om_heis V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_aut V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_cont V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unit V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_split V W χ χ' ha
  · rw [hne V W χ χ' ha.1, hne V W χ (χ' * ν) ha.1]; exact W₀.twW V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne V W (χ * ν) χ' ha.1]; exact W₀.twV V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne W V χ' χ ha.1.symm]; exact W₀.om_swap V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unr V W χ χ' ha
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).1 _ (heq V W χ (χ' * ν) (equalRankSplittingCharsAdmissible_mul_right ha hν h0))
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).2 _ (heq V W (χ * ν) χ' (equalRankSplittingCharsAdmissible_mul_left ha hν h0))

end GlobalTheory.Mem.WeilEqRank

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilOnEqExOfKnownTheorem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.OrientedCoord GlobalTheory.Mem.WeilTransport
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilEqRank

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isCoord_coord (S T : HSp D) (hr : S.rank ≤ T.rank) : IsCoord S T S T (coord S T) := {
  cont := continuous_coord S T
  cont' := continuous_coord_symm S T
  sympl := symplOH_eq S T hr
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨(γ * S.gram⁻¹)ᵀ, (coord_ratW S T γ).symm⟩
    · rintro ⟨γ, hγ⟩
      have hγ' : ratW S T γ = coord S T x := hγ
      refine ⟨γᵀ * S.gram, ?_⟩
      change ratW T S _ = x
      rw [← coord_symm_ratW, hγ', AddEquiv.symm_apply_apply]
  inf x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  fin x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  part a x h i j := by
    show a * ∑ k, x j k * incA D (S.gram⁻¹ k i) = ∑ k, x j k * incA D (S.gram⁻¹ k i)
    simp only [Finset.mul_sum, ← mul_assoc, h] }

theorem weilOnEqEx_of_weilRepresentation : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilOnEqEx D := by
  intro hP D ψ hψ V W χ χ' ⟨hr, h1, h2, h3, h4⟩
  obtain ⟨om, H⟩ := hP D ψ V W χ χ' hψ h1.1 h2.1 h3 h4
  refine exists_isWeilOn_of_coord (isCoord_coord V W hr.le) H (MonoidHom.id _) continuous_id
    (fun g h x => (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x) (fun _ a _ b => ⟨a, b⟩)
    fun e g h hg hh x y hx hy => ⟨x, y, hg, hh, hx, hy, ?_⟩
  unfold splitFacO splitFac
  rw [if_pos hr.le]

end GlobalTheory.Mem.WeilEqRank

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicWeilRepresentationWithRulesExists
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationRulesHold
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmEqSelfOfLatticeStable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem om_eq_self_of_lattice_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D), IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → splitFacO χS χT x y = 1 → (∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), actO S T g⁻¹ h⁻¹ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f) → om (g, h) f = f := by
  intro D ψ S T χS χT om hW e he g h hg hh x y hx hy h1 hL f hf hfix
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1
  rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hdual
  have hfin := @GlobalTheory.SplitScalar.latO_fin D S T (L0c D S) (L0c D T)
  have key := om_eq_sum hW he hf hfix hg hh hx hy (R := {0})
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨hL 0 (zero_mem _), GlobalTheory.SplitScalar.isHalf_zero e⟩)
    (fun w hw hwe => by
      refine ⟨0, ⟨Finset.mem_singleton_self _, ?_⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩
      rw [sub_zero, hdual w (GlobalTheory.SplitScalar.half_fin he hwe)]
      intro u hu
      rw [← symplO_actO S T g⁻¹ h⁻¹]
      exact (hdual _ (hfin hw)).1 hw _ (hL u hu))
    (fun w hw _ => hL w hw)
  rw [key, h1, Finset.sum_singleton, Finset.card_singleton, GlobalTheory.SplitScalar.heisO_zero]
  simp

end GlobalTheory.SplitHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActOMemLatOOfStab
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatStabAct

open GlobalTheory.AdelicLatMove

variable {D : D7}

def latCoord (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) where
  carrier := L0c D V
  add_mem' := by
    intro a b ha hb
    show ∑ i, (a i + b i) • V.frame i ∈ V.L0
    simp only [add_smul, Finset.sum_add_distrib]
    exact V.L0.add_mem ha hb
  zero_mem' := by
    show ∑ i, (0 : D.host.E) • V.frame i ∈ V.L0
    simp
  smul_mem' := by
    intro c a ha
    show ∑ i, (c • a i) • V.frame i ∈ V.L0
    simp only [smul_assoc, ← Finset.smul_sum]
    exact V.L0.smul_mem c ha

def swapF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom

theorem swap_mem_hatL {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (y : Fin n → Af D.host.F ⊗[D.host.F] D.host.E)
    (hy : y ∈ latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E))) :
    (fun i => swapF D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact pure_mem_hatL Λ a ha x hx
  | zero => simp only [Pi.zero_apply, map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => simp only [Pi.add_apply, map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | neg a _ ha => simp only [Pi.neg_apply, map_neg]; exact Submodule.neg_mem _ ha

theorem mulVec_pure_mem (V : HSp D) (g : GA D V) (hg : g ∈ KsphC V ∅) (x : Fin V.rank → D.host.E)
    (hx : x ∈ L0c D V) :
    (mt V g).map (toEAf D) *ᵥ (fun i => x i ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (latCoord V) := by
  have h1 : (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V) :=
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, hx, rfl⟩
  have h2 := swap_mem_hatL (latCoord V) _ ((hg.2.1 _).1 h1)
  convert h2 using 1
  funext i
  rw [RingHom.map_mulVec]
  congr 1

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem fin_smul_gen (β α : Af D.host.F) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) •
      (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] M i j : WO S T) =
      Matrix.of fun i j => (pairA D.host.F 0 (β * α)) ⊗ₜ[D.host.F] M i j := by
  ext i j
  change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  exact Prod.ext (mul_zero _) rfl

theorem fin_smul_mem {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {β : Af D.host.F} (hβ : β ∈ intAf D.host.F)
    (h0 : ∀ v, ¬ P v → evalV D.host.F v β = 0) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) • u ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β * α, fun w => ?_, fun w hw => ?_, a, ha, s, hs, t, ht,
      fin_smul_gen β α (fun i j => a * t i * ∑ k, star (s k) * S.gram k j)⟩
    · rw [map_mul]; exact mul_mem (hβ w) (hα w)
    · rw [map_mul, h0 w hw, zero_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem actO_mem_latO_of_stab : ∀ (D : D7) (S T : HSp D), ∀ g ∈ KsphC S ∅, ∀ h ∈ KsphC T ∅, ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop), ∀ u ∈ latO S T (L0c D S) (L0c D T) P, actO S T g h u ∈ latO S T (L0c D S) (L0c D T) P := by
  intro D S T g hg h hh P u hu
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 1
    have e2 := fin_smul_gen (S := S) (T := T) α (1 * 1) (fun i j => a * t i * ∑ k, star (s k) * S.gram k j)
    rw [← e, mul_one, mul_one] at e2
    have e3 : ∀ (c : AE D) (x : WO S T), actO S T g h (c • x) = c • actO S T g h x := fun c x => by
      simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
    rw [← e2, e3, actO_rankOne]
    exact fin_smul_mem hα h0 (rankOne_mem_latO S T (latCoord S) (latCoord T) a ha _
      (mulVec_pure_mem S g hg s hs) _ (mulVec_pure_mem T h hh t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

end GlobalTheory.LatStabAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationRulesHold
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilRule

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem isAdmissibleSplittingCharPair_symm {V W : HSp D} {χ χ' : IdC D} (ha : admitted V W χ χ') : admitted W V χ' χ :=
  ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩

theorem resEta_one (D : D7) : ResEta D 1 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ _ => by simp⟩

theorem isAdmissibleSplittingCharPair_mul_twist {V W : HSp D} {χ χ' ν ν' : IdC D} (ha : admitted V W χ χ') (h1 : IsHC D ν) (h2 : IsHC D ν')
    (r1 : ResEta D ν 0) (r2 : ResEta D ν' 0) : admitted V W (χ * ν) (χ' * ν') := by
  obtain ⟨C, hC⟩ := (GlobalTheory.Mem.HeckeExp.hecke_exp_laws D).1
  exact ⟨ha.1, (hC _).1 (C.mul_mem ((hC _).2 ha.2.1) ((hC _).2 h1)), (hC _).1 (C.mul_mem ((hC _).2 ha.2.2.1) ((hC _).2 h2)),
    resEta_mul ha.2.2.2.1 r1, resEta_mul ha.2.2.2.2 r2⟩

theorem twist_small (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' ν ν' : IdC D} (ha : admitted V W χ χ') (hr : V.rank < W.rank)
    (h1 : IsHC D ν) (h2 : IsHC D ν') (r1 : ResEta D ν 0) (r2 : ResEta D ν' 0)
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om)
    (H' : IsWeilOn ψ V W (χ * ν) (χ' * ν') om') {g h x y} (hx : IsDetRoot V g x) (hy : IsDetRoot W h y) :
    om' (g, h) = ((((ν' x)⁻¹ * ν y : Circle) : ℂ)) • om (g, h) := by
  obtain ⟨o, ho, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ V W χ χ' om ha hr H
  obtain ⟨o', ho', e'⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ V W _ _ om' (isAdmissibleSplittingCharPair_mul_twist ha h1 h2 r1 r2) hr H'
  obtain ⟨o'', ho'', e''⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ V W χ χ' ν ν' o ho h1.1 h2.1 r1 r2
  obtain ⟨c, -, -, hc, -, -, -, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  refine LinearMap.ext fun Φ => Subtype.ext (funext fun w => ?_)
  obtain ⟨u, rfl⟩ := c.surjective w
  have hf : IsThetaFunO ψ V W fun x => Φ.1 (toTWsmall V W x) := by
    simpa only [hc] using (hth ψ Φ.1).2 (mem_ThS.1 Φ.2)
  have k := congrFun (GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ V W _ _ o' o'' ho' ho'' (g, h) _ hf) u
  rw [e', e'' g h x y hx hy, LinearMap.smul_apply, e] at k
  rw [hc]
  exact k

theorem exists_swap (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' : IdC D} (hne : V.rank ≠ W.rank)
    {om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om) :
    ∃ om' : GA D W × GA D V →* Module.End ℂ (ThS ψ W V), IsWeilOn ψ W V χ' χ om' ∧
      ∀ g h Φ, om' (h, g) (WeilSwap.trEquiv ψ hne Φ) = WeilSwap.trEquiv ψ hne (om (g, h) Φ) := by
  obtain ⟨om', H', e⟩ := WeilSwap.exists_isWeilOn_swap D ψ hψ V W χ χ' om hne H
  exact ⟨om', H', fun g h Φ => Subtype.ext (funext fun y => e g h Φ _ (fun _ => rfl) y.transpose)⟩

theorem twist (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' ν ν' : IdC D} (ha : admitted V W χ χ')
    (h1 : IsHC D ν) (h2 : IsHC D ν') (r1 : ResEta D ν 0) (r2 : ResEta D ν' 0)
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om)
    (H' : IsWeilOn ψ V W (χ * ν) (χ' * ν') om') {g h x y} (hx : IsDetRoot V g x) (hy : IsDetRoot W h y) :
    om' (g, h) = (((if V.rank < W.rank then (ν' x)⁻¹ * ν y else (ν y)⁻¹ * ν' x : Circle) : ℂ)) • om (g, h) := by
  rcases ha.1.lt_or_gt with hr | hr
  · rw [if_pos hr]; exact twist_small hψ ha hr h1 h2 r1 r2 H H' hx hy
  · rw [if_neg hr.not_gt]
    obtain ⟨o, ho, e⟩ := exists_swap hψ ha.1 H
    obtain ⟨o', ho', e'⟩ := exists_swap hψ ha.1 H'
    refine LinearMap.ext fun Φ => (WeilSwap.trEquiv ψ ha.1).injective ?_
    rw [← e', twist_small hψ (isAdmissibleSplittingCharPair_symm ha) hr h2 h1 r2 r1 ho ho' hy hx, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, e]

theorem unique (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' : IdC D} (ha : admitted V W χ χ')
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om)
    (H' : IsWeilOn ψ V W χ χ' om') : om' = om := by
  refine MonoidHom.ext fun ⟨g, h⟩ => ?_
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D V g
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D W h
  have := twist hψ ha (isHC_one D) (isHC_one D) (resEta_one D) (resEta_one D) H (by simpa only [mul_one] using H') hx hy
  simpa using this

theorem map_eq_one_of_supp {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {a x : R} (ha : φ a = 0)
    (hx : a * (x - 1) = x - 1) : φ x = 1 := by
  have := congrArg φ hx
  rw [map_mul, ha, zero_mul, map_sub, map_one] at this
  exact sub_eq_zero.1 this.symm

theorem unramAt_of_outside {χ : IdC D} {Z : Finset (HeightOneSpectrum (𝓞 D.host.F))} (h : UnramOutside D χ Z)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ Z) {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) : UnramAt ε χ := by
  obtain ⟨β, rfl, -, h0⟩ := hε
  intro x hx i1 i2
  refine h x (map_eq_one_of_supp (infPart D) (TensorProduct.zero_tmul _ _) hx) i1 i2 fun w hw => ?_
  refine map_eq_one_of_supp
    ((Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)).toRingHom.comp (finPart D)) ?_ hx
  change evalV D.host.F w β ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  rw [h0 w fun e => hv (e ▸ hw), TensorProduct.zero_tmul]

theorem fixes_local {S T : HSp D} {χS χT : IdC D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (uS : UnramAt ε χS) (uT : UnramAt ε χT) {g : GA D S} {h : GA D T} (hg : g ∈ KsphC S ∅) (hh : h ∈ KsphC T ∅)
    (sg : SuppPl ε S g) (sh : SuppPl ε T h) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hv : ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun w => w = v), heisO ψ S T u f = f) : om (g, h) f = f := by
  obtain ⟨KS, hKS, -⟩ := GlobalTheory.Mem.Ksph.exists_subgroup_ksph D S ∅
  obtain ⟨KT, hKT, -⟩ := GlobalTheory.Mem.Ksph.exists_subgroup_ksph D T ∅
  have hg' : g⁻¹ ∈ KsphC S ∅ := by rw [← hKS] at hg ⊢; exact KS.inv_mem hg
  have hh' : h⁻¹ ∈ KsphC T ∅ := by rw [← hKT] at hh ⊢; exact KT.inv_mem hh
  by_cases hs : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e, he, heq⟩ := hs
    obtain ⟨x, hx, hx1⟩ := GlobalTheory.Mem.DetUnit.exists_isDetAt_unram D S ε e he heq g hg
    obtain ⟨y, hy, hy1⟩ := GlobalTheory.Mem.DetUnit.exists_isDetAt_unram D T ε e he heq h hh
    have he' : cA D e * cA D e = cA D e := by rw [← map_mul, he.1]
    have heε : algebraMap (AF D.host.F) (AE D) ε * e = e := by rw [← heq]; linear_combination he.1 + he.2.1
    have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + he.2.1
    refine GlobalTheory.SplitHecke.om_eq_self_of_lattice_stable D ψ S T χS χT om H e he g h (fun i j => by rw [heq]; exact sg i j)
      (fun i j => by rw [heq]; exact sh i j) x y hx hy (by rw [splitFacO, hx1 _ uT, hy1 _ uS, inv_one, mul_one])
      (GlobalTheory.LatStabAct.actO_mem_latO_of_stab D S T _ hg' _ hh' _) f hf fun u hu hh => hv u ?_
    rcases hh with hh | hh
    · have := (GlobalTheory.PlaceModel.idem_smul_mem hε he.1 heε hu).1
      rwa [show e • u = u from Matrix.ext hh] at this
    · have := (GlobalTheory.PlaceModel.idem_smul_mem hε he' heε' hu).1
      rwa [show cA D e • u = u from Matrix.ext hh] at this
  · obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
    have k := GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ H.std S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
      χS χT om ⟨η, e1, e4, e3, e2⟩ H v ε ⟨hε, hs⟩ uS uT g h sg sh
    rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at k
    refine k (fun u => ⟨GlobalTheory.LatStabAct.actO_mem_latO_of_stab D S T _ hg _ hh _ u, fun hu => ?_⟩) f hf hv
    have := GlobalTheory.LatStabAct.actO_mem_latO_of_stab D S T _ hg' _ hh' _ _ hu
    have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
    rw [inv_inv, inv_inv] at e
    rwa [e] at this

theorem latO_mono {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P Q : HeightOneSpectrum (𝓞 D.host.F) → Prop} (h : ∀ w, P w → Q w) : latO S T LS LT P ≤ latO S T LS LT Q :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, h0, k⟩ => ⟨α, hα, fun w hw => h0 w fun e => hw (h w e), k⟩

theorem fixes_oriented {S T : HSp D} {χS χT : IdC D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) {Z : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (uS : UnramOutside D χS Z) (uT : UnramOutside D χT Z) {g : GA D S} {h : GA D T} (hg : g ∈ KsphC S Z) (hh : h ∈ KsphC T Z)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hv : ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun w => w ∉ Z), heisO ψ S T u f = f) : om (g, h) f = f := by
  let K : Subgroup (GA D S × GA D T) :=
    { carrier := {p | om p f = f}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change om (a * b) f = f
        rw [map_mul, Module.End.mul_apply, show om b f = f from hb, show om a f = f from ha]
      inv_mem' := fun {a} ha => by
        change om a⁻¹ f = f
        conv_lhs => rw [← show om a f = f from ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hK : IsClosed (K : Set (GA D S × GA D T)) :=
    isClosed_eq (continuous_pi fun w => H.om_cont f hf w) continuous_const
  have hl : ∀ v, v ∉ Z → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun w => w = v), heisO ψ S T u f = f := fun v hvZ u hu =>
    hv u (latO_mono (fun w (e : w = v) => e ▸ hvZ) hu)
  have one : ∀ V : HSp D, (1 : GA D V) ∈ KsphC V ∅ := fun V => by
    obtain ⟨KV, hKV, -⟩ := GlobalTheory.Mem.Ksph.exists_subgroup_ksph D V ∅
    rw [← hKV]; exact KV.one_mem
  have sone : ∀ (V : HSp D) ε, SuppPl ε V 1 := fun V ε i j => by simp [Formalism.L2.Theta.mt]
  have k1 : g ∈ K.comap (MonoidHom.inl _ _) :=
    GlobalTheory.LevelClosure.ksph_le_of_isClosed D S Z _ (hK.preimage (continuous_id.prodMk continuous_const))
      (fun v hvZ ε hε g hg sg => fixes_local H hε (unramAt_of_outside uS hvZ hε) (unramAt_of_outside uT hvZ hε) hg (one T) sg
        (sone T ε) hf (hl v hvZ)) g hg
  have k2 : h ∈ K.comap (MonoidHom.inr _ _) :=
    GlobalTheory.LevelClosure.ksph_le_of_isClosed D T Z _ (hK.preimage (continuous_const.prodMk continuous_id))
      (fun v hvZ ε hε h hh sh => fixes_local H hε (unramAt_of_outside uS hvZ hε) (unramAt_of_outside uT hvZ hε) (one S) hh
        (sone S ε) sh hf (hl v hvZ)) h hh
  have : (g, h) ∈ K := by simpa using K.mul_mem k1 k2
  exact this

theorem fixes_small (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' : IdC D} (ha : admitted V W χ χ') (hr : V.rank < W.rank)
    {om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (H : IsWeilOn ψ V W χ χ' om)
    {Z : Finset (HeightOneSpectrum (𝓞 D.host.F))} (u1 : UnramOutside D χ Z) (u2 : UnramOutside D χ' Z)
    {g : GA D V} {h : GA D W} (hg : g ∈ KsphC V Z) (hh : h ∈ KsphC W Z) (Φ : ThS ψ V W)
    (hv : ∀ u ∈ latVWS V W Z, Heisenberg₂ ψ V W u Φ.1 = Φ.1) : om (g, h) Φ = Φ := by
  obtain ⟨o, ho, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ V W χ χ' om ha hr H
  obtain ⟨c, -, -, hc, -, -, hhe, hth, hl⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  have k := fixes_oriented ho u1 u2 hg hh ((hth ψ Φ.1).2 (mem_ThS.1 Φ.2)) fun u hu => by
    rw [hhe, hv _ (hl Z u hu)]
  simp only [hc] at k
  rw [e] at k
  refine Subtype.ext (funext fun w => ?_)
  obtain ⟨u, rfl⟩ := c.surjective w
  rw [hc]
  exact congrFun k u

theorem transpose_mem_latVWS {V W : HSp D} (hne : V.rank ≠ W.rank) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    {u : WA V W} (hu : u ∈ latVWS V W Z) : u.transpose ∈ latVWS W V Z := by
  have : latVWS V W Z ≤ (latVWS W V Z).comap (Matrix.transposeAddEquiv _ _ _).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, h0, a, ha, x, hx, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, y, hy, x, hx, Matrix.ext fun i j => ?_⟩
    change _ ⊗ₜ _ = _ ⊗ₜ _
    congr 1
    rcases hne.lt_or_gt with hr | hr
    · rw [if_pos hr.le, if_neg hr.not_ge]; ring
    · rw [if_neg hr.not_ge, if_pos hr.le]; ring
  exact this hu

theorem weilRules : ∀ D : D7, WeilRules D := by
  intro D ψ hψ Wc
  refine ⟨fun V W χ χ' ν ha h1 r1 g h x hx => ?_, fun V W χ χ' ν ha h1 r1 g h y hy => ?_,
    fun V W χ χ' ha g h Φ Φ' e x => ?_, fun V W χ χ' ha Z u1 u2 g hg h hh Φ hv => ?_⟩
  · obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D W h
    have := twist hψ ha (isHC_one D) h1 (resEta_one D) r1 (Wc.weil V W χ χ' ha)
      (Wc.weil V W _ _ (isAdmissibleSplittingCharPair_mul_twist ha (isHC_one D) h1 (resEta_one D) r1)) hx hy
    simpa only [mul_one, MonoidHom.one_apply, inv_one, one_mul] using this
  · obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D V g
    have := twist hψ ha h1 (isHC_one D) r1 (resEta_one D) (Wc.weil V W χ χ' ha)
      (Wc.weil V W _ _ (isAdmissibleSplittingCharPair_mul_twist ha h1 (isHC_one D) r1 (resEta_one D))) hx hy
    simpa only [mul_one, MonoidHom.one_apply, inv_one, one_mul] using this
  · obtain ⟨o, ho, k⟩ := WeilSwap.exists_isWeilOn_swap D ψ hψ V W χ χ' _ ha.1 (Wc.weil V W χ χ' ha)
    rw [unique hψ (isAdmissibleSplittingCharPair_symm ha) ho (Wc.weil W V χ' χ (isAdmissibleSplittingCharPair_symm ha))]
    exact k g h Φ Φ' e x
  · rcases ha.1.lt_or_gt with hr | hr
    · exact fixes_small hψ ha hr (Wc.weil V W χ χ' ha) u1 u2 hg hh Φ hv
    · obtain ⟨o, ho, k⟩ := exists_swap hψ ha.1 (Wc.weil V W χ χ' ha)
      refine (WeilSwap.trEquiv ψ ha.1).injective ?_
      rw [← k]
      refine fixes_small hψ (isAdmissibleSplittingCharPair_symm ha) hr ho u2 u1 hh hg _ fun u hu => ?_
      refine (WeilSwap.heis_transpose ψ ha.1.symm u Φ.1).symm.trans ?_
      rw [hv _ (transpose_mem_latVWS ha.1.symm Z hu)]
      rfl

end GlobalTheory.Mem.WeilRule

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationRulesHoldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationRules_hold : ∀ D : D7, WeilRules D := by
  first | exact @GlobalTheory.Mem.WeilRule.weilRules | exact GlobalTheory.Mem.WeilRule.weilRules | (intros; apply GlobalTheory.Mem.WeilRule.weilRules <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicWeilRepresentationWithRulesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th

namespace GlobalTheory.Mem.WeilExists

theorem weilEx_of_weilRepresentation : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilEx D := fun h D =>
  weilEx_of
    (GlobalTheory.Mem.WeilTransport.weilCoreEx_of_datum D fun ψ hψ S T χS χT h1 h2 h3 h4 => h D ψ S T χS χT hψ h1 h2 h3 h4)
    (GlobalTheory.T.weilRepresentationRules_hold D)

end GlobalTheory.Mem.WeilExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicWeilRepresentationWithRulesExistsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicWeilRepresentation_with_rules_exists : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilEx D := by
  first | exact @GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation | exact GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation | (intros; apply GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureLeOfCover
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselIntegrable

theorem measure_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] {𝓕 K : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hK : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) : μ 𝓕 ≤ μ K := by
  rw [h.measure_eq_tsum K]
  refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hK n
  exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩

theorem norm_besChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) {A B : HSp D}
    {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (n : GA D B) : ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
    rw [e]
    exact hψ _
  · exact norm_one

theorem besInt : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, BesInt D := by
  intro hP D θ hθ ψ hψ A B ι hι d μ 𝓕 hq μN 𝓕N hμN h𝓕N s hs φ F hφ hF hA
  obtain ⟨-, a2, a3, a4, a5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, b2, b3, b4, b5, -, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have : Countable (NFlagQ B d.e) :=
    Function.Injective.countable (f := fun x : NFlagQ B d.e => (⟨x.1.1, x.2⟩ : GQ B))
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ B => z.1) h))
  have : SecondCountableTopology (NFlag B d.e) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨⟨K, hK, hcov⟩, -⟩ := GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D B d.ρ d.e d.e_iso
  have hfin : μN 𝓕N < ⊤ := (measure_le_of_cover _ μN h𝓕N hcov).trans_lt hK.measure_lt_top
  obtain ⟨C, hC⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ hF.1 hF.2
  obtain ⟨s', hs', hs'', -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  have hsc : Continuous s := by
    rw [show s = s' from funext fun h => (hs'' h _).1 (hs h)]
    exact hs'
  have hχ := (GlobalTheory.T.besselCharacter_generic_character_laws D ψ hψ A B ι hι d).2.2.1
  have hb : ∀ (h : GA D A) (n : NFlag B d.e), ‖star (φ h) * F ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B))‖ ≤ ‖φ h‖ * C := fun h n => by
    rw [norm_mul, norm_mul, norm_star, norm_star, norm_besChar hψ.1.2.1, mul_one]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hc : Continuous fun p : GA D A × NFlag B d.e => star (φ p.1) * F ((p.2 : GA D B) * s p.1 * (d.y : GA D B)) *
      star (besChar ψ d (p.2 : GA D B)) :=
    ((hφ.cont.comp continuous_fst).star.mul (hF.1.cont.comp
      (((continuous_subtype_val.comp continuous_snd).mul (hsc.comp continuous_fst)).mul continuous_const))).mul
      (hχ.comp continuous_snd).star
  refine ⟨fun h => Measure.integrableOn_of_bounded (M := ‖φ h‖ * C) hfin.ne
    (hc.comp (Continuous.prodMk_right h)).measurable.aestronglyMeasurable (.of_forall (hb h)), ?_⟩
  have hcusp : IsCuspForm θ A φ := ⟨hφ, hA.elim (fun h r C hC => absurd hC (h r C)) id⟩
  have hint := GlobalTheory.Mem.Th.petInt_of_cuspRapidDecay hP D θ hθ A μ 𝓕 hq (fun _ => 1) φ (isAutFunSm_const θ A 1) hcusp
  simp only [star_one, one_mul] at hint
  have : IsFiniteMeasure (μN.restrict 𝓕N) := isFiniteMeasure_restrict.2 hfin.ne
  refine Integrable.mono' ((hint.norm.mul_const C).mul_const (μN.real 𝓕N))
    (hc.stronglyMeasurable.integral_prod_right' (ν := μN.restrict 𝓕N)).aestronglyMeasurable (.of_forall fun h => ?_)
  exact norm_setIntegral_le_of_norm_le_const hfin fun n _ => hb h n

end GlobalTheory.Mem.BesselIntegrable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealPlaceRecordTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_realPlace_record_tied :
    (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) →
    ∀ D : D7, ∃ A : ProvA, ProvisionCompatibility D A := by
  intro H D
  classical
  choose grp hgrp using fun p q : ℕ =>
    GlobalTheory.DetSqrtCover.exists_grpData_map_haar p q (D.cd.cd p q) (D.cd.haar p q)
  have key : ∀ (p q : ℕ) (lam : Ix p q → ℚ), ∃ R : DSRep (grp p q),
      IsParam lam → HasParam R lam := by
    intro p q lam
    by_cases h : IsParam lam
    · obtain ⟨R, hR⟩ := H p q (grp p q) lam h
      exact ⟨R, fun _ => hR⟩
    · obtain ⟨R, -⟩ := H p q (grp p q) _ (realPlaceStdParam_isParam p q)
      exact ⟨R, fun h' => absurd h' h⟩
  choose ds hds using key
  exact ⟨⟨grp, fun p q r s => Classical.choice (GlobalTheory.T.nonempty_fockModel_unitary_dual_pair p q r s _ _ _), ds⟩,
    ⟨hgrp, fun p q lam h => by first | exact hds p q lam h | exact fun _ => hds p q lam h⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypAddOfDiscreteSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.TypeSum in
theorem GlobalTheory.TypeSum.typAdd_of_discreteSeries : ∀ D : D7, (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → TypAdd D := by
  intro D hex huniq θ hθ V hV τ S hS
  obtain ⟨lam₀, ε₀, hE₀, hP₀, hp, hq⟩ := hS
  refine ⟨(GlobalTheory.TypeAtTest.isTypeAt_zero θ V).2 ?_, fun φ φ' _ _ h h' => ?_⟩
  · obtain ⟨H, i1, i2, σ, hσ⟩ := hex _ ε₀ lam₀ hP₀
    obtain ⟨P, h1, h2⟩ := GlobalTheory.Published.exists_frame_of_hasSignature (hV (tauE D τ)) ε₀ hp hq
    exact ⟨H, i1, i2, σ, lam₀, ε₀, P, hE₀, hσ, h1, h2⟩
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hσ, hP, hG, hx⟩ := h
  obtain ⟨H', j1, j2, σ', lam', ε', P', hE', hσ', hP', hG', hx'⟩ := h'
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE hE₀
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE' hE₀
  obtain ⟨U, hU⟩ := huniq _ _ _ hP₀ H' H σ' σ hσ' hσ
  refine ⟨H, i1, i2, σ, _, _, P, hE, hσ, hP, hG, fun x => ?_⟩
  exact hasTypeAll_iff.1 (hasTypeAll_add_of_equiv hσ.2.2.1 U hU hP hP' hG hG'
    (f := fun g => φ (x * atTau θ V τ g)) (f' := fun g => φ' (x * atTau θ V τ g))
    (hasTypeAll_iff.2 (hx x)) (hasTypeAll_iff.2 (hx' x)))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumNormEmb
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.TopIntegrand

def extId {R : Type} [CommRing R] {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (P : Matrix (Fin n) (Fin m) R)
    (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin m) (Fin m) R := 1 + M * (x - 1) * P

theorem map_emb {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ} (M : Matrix (Fin m) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (x : Matrix (Fin n) (Fin n) R) :
    (extId M P x).map f = extId (M.map f) (P.map f) (x.map f) := by
  rw [extId, extId, Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub f),
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_one _ (map_zero f) (map_one f)]

theorem sum_norm_emb {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (P : Matrix (Fin n) (Fin m) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Matrix (Fin n) (Fin n) ℂ,
      ∑ i, ∑ j, ‖extId M P x i j‖ ≤ c * (1 + ∑ k, ∑ l, ‖x k l‖) := by
  refine ⟨∑ i, ∑ j, (‖(1 - M * P : Matrix (Fin m) (Fin m) ℂ) i j‖ + ∑ l, ∑ k, ‖M i k‖ * ‖P l j‖), by positivity, fun x => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : extId M P x = (1 - M * P) + M * x * P := by
    rw [extId, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
  have hS : 0 ≤ ∑ k, ∑ l, ‖x k l‖ := by positivity
  have hx : ∀ k l, ‖x k l‖ ≤ 1 + ∑ k, ∑ l, ‖x k l‖ := fun k l =>
    ((Finset.single_le_sum (f := fun l => ‖x k l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, ‖x k l‖) (fun _ _ => by positivity) (Finset.mem_univ k))).trans
      (by linarith)
  rw [e, Matrix.add_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add (le_mul_of_one_le_right (norm_nonneg _) (by linarith)) ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, mul_right_comm]
  exact mul_le_mul_of_nonneg_left (hx k l) (by positivity)

variable {D : D7} {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (hι : HSpace.IsIsomEmb B A ι)

abbrev emb : GA D B →* GA D A := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι

theorem matHom_emb (h : GA D B) : (matHom A (emb hι h)).1 =
    extId ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat B A ι).map (incA D)) ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat D.sp.cm B A ι).map (incA D))
      (matHom B h).1 := rfl

theorem emb_ker {S : Type} [CommRing S] (f : AF D.host.F ⊗[D.host.F] D.host.E →+* S) (h : GA D B)
    (hh : Formalism.UG.bc f (matHom B h) = 1) : Formalism.UG.bc f (matHom A (emb hι h)) = 1 := by
  have h1 : (matHom B h).1.map f = 1 := congrArg Units.val hh
  refine Units.ext ?_
  change (matHom A (emb hι h)).1.map f = 1
  rw [matHom_emb, map_emb, h1, extId, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem emb_GfC {h : GA D B} (hh : h ∈ GfC B) : emb hι h ∈ GfC A := emb_ker hι _ h hh

theorem emb_GinfC {h : GA D B} (hh : h ∈ GinfC B) : emb hι h ∈ GinfC A := emb_ker hι _ h hh

theorem infMat_emb (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) : ∃ M P, ∀ h : GA D B,
    infMat D.sp.cm.sig A.gram θ (emb hι h) = extId M P (infMat D.sp.cm.sig B.gram θ h) := by
  refine ⟨?_, ?_, fun h => ?_⟩
  rotate_left 2
  change ((matHom A (emb hι h)).1.map
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).map θ = _
  rw [matHom_emb, map_emb, map_emb]
  rfl

theorem normInf_emb (θ : InfF D) : ∃ c : ℝ, 0 ≤ c ∧ ∀ h : GA D B,
    normInf θ A (emb hι h) ≤ c * (1 + normInf θ B h) := by
  choose M P hMP using fun τ => infMat_emb hι (θ τ)
  choose c hc0 hc using fun τ => sum_norm_emb (M τ) (P τ)
  refine ⟨∑ τ, 2 * c τ, Finset.sum_nonneg fun τ _ => by have := hc0 τ; positivity, fun h => ?_⟩
  rw [Finset.sum_mul, normInf]
  refine Finset.sum_le_sum fun τ _ => ?_
  have h0 : ∑ i, ∑ j, (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖) ≤
      normInf θ B h := Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  simp only [Finset.sum_add_distrib] at h0 ⊢
  rw [← map_inv, hMP, hMP]
  have h1 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h)
  have h2 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h⁻¹)
  have h3 := mul_le_mul_of_nonneg_left h0 (hc0 τ)
  have h4 := mul_nonneg (hc0 τ) (GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h)
  nlinarith

theorem emb_moderate {θ : InfF D} (hθ : IsInfFam θ) (hc : Continuous (emb hι)) (hQ : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A)
    {φ : GA D A → ℂ} (hφ : IsAutFunSm θ A φ) :
    ∃ (N : ℕ) (C : ℝ), ∀ g, ‖φ (emb hι g)‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ N := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨S, C₀, M, hS⟩ := GlobalTheory.SmoothForms.reduction hθ ((GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ B) (U.comap (emb hι)) (hU.preimage hc)
  obtain ⟨N, hN⟩ := hφ.growth
  choose C hC using hN [] (by simp)
  obtain ⟨c, hc0, hc⟩ := normInf_emb hι θ
  refine ⟨M * N, (∑ x ∈ S, |C (emb hι x)|) * (c * (1 + |C₀|)) ^ N, fun g => ?_⟩
  obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk', e, hb⟩ := hS g
  rw [← hφ.left _ (hQ γ hγ), ← map_mul, e, map_mul, map_mul, hUφ _ hk (emb_GfC hι hk'), pow_mul, mul_assoc, ← mul_pow]
  have h1 : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M :=
    one_le_pow₀ (by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ B g)
  have h2 : normInf θ A (emb hι a) ≤ c * (1 + |C₀|) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M := by
    refine (hc a).trans ?_
    rw [mul_assoc, add_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add h1 (hb.trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans h1)))) hc0
  exact (hC _ _ (emb_GinfC hι ha)).trans (mul_le_mul ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C (emb hι x)|) (fun _ _ => abs_nonneg _) hx))
    (pow_le_pow_left₀ (GlobalTheory.SmoothForms.normInf_nonneg _) h2 N) (pow_nonneg (GlobalTheory.SmoothForms.normInf_nonneg _) N)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))

theorem topInt (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) : TopInt D := by
  intro θ hθ A B ι hι μ 𝓕 hq s hs φ φ' hφ hφ'
  obtain rfl : s = emb hι := funext fun h => (GlobalTheory.AutFunCompare.embRel_iff A B ι hι _ _).1 (hs h)
  obtain ⟨s, hc, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D A B ι hι
  have e : ∀ h, emb hι h = s h := fun h => (hrel h _).1 (hs h)
  have hc' : Continuous (emb hι) := by rw [show ⇑(emb hι) = s from funext e]; exact hc
  have hQ' : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A := fun γ hγ => e γ ▸ hQ γ hγ
  obtain ⟨N, C, hC⟩ := emb_moderate hι hθ hc' hQ' hφ
  obtain ⟨K, hK⟩ := (GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hφ'.1 hφ'.2).mul_bounded
    (ψ := fun g => φ (emb hι g)) (fun γ hγ g => by simp only [map_mul]; exact hφ.left _ (hQ' γ hγ) _) hC
  have : BorelSpace (GA D B) := ⟨rfl⟩
  refine Measure.integrableOn_of_bounded (M := K)
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B μ 𝓕 hq.1 hq.2).ne
    (((hφ.cont.comp hc').star.mul hφ'.1.cont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_mul, norm_star]
  exact hK g

end GlobalTheory.Mem.TopIntegrand

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.TowerSpaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_tow : ∀ D : D7, ∃ Tw : Tow D, (∀ j, j < D.R.m → HEq (Tw.iXYs D.R.t j) (D.sp.iXY j)) ∧
    HEq (Tw.iYXm D.R.t) (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap) := by
  intro D
  obtain ⟨Tw⟩ := nonempty_tow (GlobalTheory.WittLow.wittLowEx D)
  exact ⟨Tw, Tw.iXYs_rec, Tw.iYXm_rec⟩

end GlobalTheory.TowerSpaces
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem exists_allTied_eqTied_on_of_realised {D : D7} (ht : TypAdd D)
    (hW : ∀ ψ, IsStdChar D ψ (-1) → ∃ Wf : WeilFun D ψ, Wf.EqRank) (hT : Nonempty (Tow D)) (hX : RealisedExE D)
    (hA : ∃ A : ProvA, ProvisionCompatibility D A) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E)
    (U : Set D.what₂.Tup) (hr : RealTied D) (hR : (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y))) :
    ∃ X : ThetaX D, X.TieIo ∧ (∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
      X.petY μ j ((X.rowAF μ j x : X.cusp _) : X.AF _) (X.rowAF μ j y) = inner ℂ x y) ∧
      ∃ (A : ProvA) (a : AllTied D X A), WeilThetaCompatibility a.W ∧
      ∀ (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Tp.xi = xi →
        ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, Formalism.IndefR.Links.ChrEq (a.T.eChr c) (H.eChr c) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdAdelicChar.existsUnique_isStdChar D (-1) (Or.inr rfl)
  obtain ⟨Wf, hE⟩ := hW ψ hψ
  obtain ⟨Tw⟩ := hT
  obtain ⟨Rc, hc, hio, hi⟩ := hR θ hθ ψ hψ Wf
  obtain ⟨X, T, W, B, rfl, h⟩ := hX θ hθ ψ hψ Wf hE Tw Rc
  obtain ⟨A, hA⟩ := hA
  obtain ⟨K, -⟩ := h.kfin
  refine ⟨X, h.tieIo hio, fun μ hμ j hj x y => ?_, A, ⟨T, h.afTiedSm, h.typTied ht, W, h.weilUnrTied, K, h.phiUp, B, hr, hA⟩,
    h.eqTied, fun nch Tp e => ?_⟩
  · obtain ⟨⟨m, hm⟩, h2⟩ := hi μ hμ j hj x y
    have e := T.pet _ (D.sp.Y_sig j) m.1 m.2 hm (X.rowAF μ j x) (X.rowAF μ j y)
    unfold ThetaX.petY
    rw [e, (h2 m hm).2, h.row, h.row, h.mY, ← h.petC_eq]
    simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]
  · exact GlobalTheory.TowerCharRead.exists_thetaChrTied D C nch Tp X T (e ▸ h.chrRead hc)

theorem exists_allTied_eqTied_on : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup), RealTied D → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) → ∃ X : ThetaX D, X.TieIo ∧ (∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, X.petY μ j ((X.rowAF μ j x : X.cusp _) : X.AF _) (X.rowAF μ j y) = inner ℂ x y) ∧ ∃ (A : ProvA) (a : AllTied D X A), WeilThetaCompatibility a.W ∧ ∀ (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Tp.xi = xi → ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, Formalism.IndefR.Links.ChrEq (a.T.eChr c) (H.eChr c) := by
  intro hW hC hex huniq hds D C xi U hr hR
  exact exists_allTied_eqTied_on_of_realised (GlobalTheory.TypeSum.typAdd_of_discreteSeries D hex huniq)
    (GlobalTheory.Mem.WeilEqRank.exists_weilFun_eqRank D (GlobalTheory.T.adelicWeilRepresentation_with_rules_exists hW D) (GlobalTheory.Mem.WeilEqRank.weilOnEqEx_of_weilRepresentation hW D)
      (GlobalTheory.Mem.WeilTwist.weilTwEq D))
    ((GlobalTheory.TowerSpaces.exists_tow D).elim fun Tw _ => ⟨Tw⟩)
    (GlobalTheory.Mem.TrueRecordEq.exists_realisedE D (petInt_of_cuspRapidDecay hC D) (GlobalTheory.Mem.TopIntegrand.topInt hC D)
      (GlobalTheory.Mem.BesselIntegrable.besInt hC D) (GlobalTheory.Mem.Lift.liftAut hC D) (GlobalTheory.Mem.Lift.liftAutEq hC D))
    (GlobalTheory.exists_realPlace_record_tied hds D) C xi U hr hR

end GlobalTheory.Mem.Th
