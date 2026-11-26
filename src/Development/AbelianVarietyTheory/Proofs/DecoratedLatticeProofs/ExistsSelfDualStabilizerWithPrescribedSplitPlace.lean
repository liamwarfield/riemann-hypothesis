module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitOnto

variable {D : D7}

theorem eq_zero_at_off (P : Pl D → Prop) {a : AE D} (h1 : a ∈ idAt D P) (h2 : a ∈ idOff D P) : a = 0 := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).1
  rw [← (hA a).1 h1]
  exact (hO a).1 h2

theorem mulVec_off {S : HSp D} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : mt S b *ᵥ y = y := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  have key : (mt S b - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    apply eq_zero_at_off P
    · exact Ideal.mul_mem_left _ _ (hy j)
    · exact Ideal.mul_mem_right _ _ (by simpa using hb i j)
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

theorem moves_off {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) :
    Moves S b L L P := by
  intro y hy
  rw [mulVec_off hb hy]

theorem moves_one {S : HSp D} {L : Lat S} {P : Pl D → Prop} : Moves S 1 L L P := by
  intro y _
  rw [PlacesAdeles.mt_one, Matrix.one_mulVec]

theorem moves_list_prod {S : HSp D} {L : Lat S} {P : Pl D → Prop} :
    ∀ l : List (GA D S), (∀ a ∈ l, Moves S a L L P) → Moves S l.prod L L P
  | [], _ => by rw [List.prod_nil]; exact moves_one
  | a :: l, h => by
    rw [List.prod_cons]
    exact PlacesAdeles.moves_mul (h a List.mem_cons_self) (moves_list_prod l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem prod_ofFn_single {M : Type*} [Monoid M] :
    ∀ {r : ℕ} (f : Fin r → M) (i : Fin r), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | r + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · have hprod : (List.ofFn (fun j : Fin r => f j.succ)).prod = 1 := by
        apply List.prod_eq_one
        rw [List.forall_mem_ofFn_iff]
        exact fun j => h j.succ (Fin.succ_ne_zero j)
      rw [hprod, mul_one]
    · rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact prod_ofFn_single (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

def locHom (S : HSp D) {k : Type} [Ring k] (f : AE D →+* k) : GA D S →* Matrix (Fin S.rank) (Fin S.rank) k where
  toFun a := (mt S a).map f
  map_one' := by rw [PlacesAdeles.mt_one]; exact Matrix.map_one f f.map_zero f.map_one
  map_mul' a b := by rw [PlacesAdeles.mt_mul]; exact Matrix.map_mul

section Place

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_off (q : SplitPt D k) {a : AE D} (ha : a ∈ idOff D (· = q.v)) : q.pr a = 0 := by
  have h1 : q.e * a = 0 := eq_zero_at_off (· = q.v)
    (Ideal.mul_mem_right a _ (FrameLat.e_mem_idAt (p := q))) (Ideal.mul_mem_left _ q.e ha)
  have h2 : q.pr q.e = 1 := by rw [← FrameLat.sec_one (p := q), q.pr_sec]
  calc q.pr a = q.pr q.e * q.pr a := by rw [h2, one_mul]
    _ = 0 := by rw [← map_mul, h1, map_zero]

theorem map_off (q : SplitPt D k) {S : HSp D} {b : GA D S} (hb : b ∈ grpOff S (· = q.v)) :
    (mt S b).map q.pr = 1 := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  ext i j
  have h := pr_off q (hb i j)
  rw [map_sub, sub_eq_zero] at h
  rw [Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem one_place (S : HSp D) (N : Lat S) (hN : IsSelfDualC S N) (q : SplitPt D k) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) (hI : IntIn q S F N) (x : GL Y k) (hx : x ∈ GlobalTheory.SplitWeil.KO k Y) :
    ∃ g, InK S N (· = q.v) g ∧ (mt S g).map q.pr = F.β * x.val * F.γ := by
  classical
  have H := (GlobalTheory.LocGrp.local_groups D k (GlobalTheory.LocMod.Place.ofSplitPt q)).1 S Y F
  choose glf hglf using fun gk => (H.1 gk).exists
  let gl : GL Y k →* GA D S := MonoidHom.mk' glf fun a b =>
    (H.1 (a * b)).unique (hglf (a * b)) (H.2.2 _ _ _ _ (hglf a) (hglf b))
  let β : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun g => (hglf g).1, fun g => (hglf g).2⟩
  obtain ⟨Λ, -, hΛ, hK⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y β N hN
  have hmem : ∀ y : Y → k, y ∈ Λ ↔ ∀ j, y j ∈ 𝒪[k] := fun y => (hΛ y).trans (hI y).symm
  obtain ⟨x₀, rfl⟩ := hx
  have hint : ∀ (z : GL Y 𝒪[k]) (y : Y → k), (∀ j, y j ∈ 𝒪[k]) →
      ∀ j, (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z • y) j ∈ 𝒪[k] := by
    intro z y hy j
    change ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z).val *ᵥ y) j ∈ 𝒪[k]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun l _ => mul_mem (z.val j l).2 (hy l)
  have hstab : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x₀ • Λ = Λ := by
    ext y
    rw [GlobalTheory.LatPair.mem_smul_iff, hmem, hmem]
    constructor
    · intro h
      have := hint x₀ _ h
      rwa [smul_inv_smul] at this
    · intro h
      rw [← map_inv]
      exact hint x₀⁻¹ y h
  exact ⟨β.gl _, (hK _).2 hstab, (hglf _).2⟩

end Place

theorem exists_of_local : ∀ {D : D7} (S : HSp D) (N : Lat S), IsSelfDualC S N → ∀ {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i)), Function.Injective (fun i => (q i).v) → (∀ i, IntIn (q i) S (F i) N) → ∀ x : (i : Fin r) → GL (Y i) (k i), (∀ i, x i ∈ GlobalTheory.SplitWeil.KO (k i) (Y i)) → ∃ g, InK S N (fun p => ∃ i, (q i).v = p) g ∧ ∀ i, (mt S g).map (q i).pr = (F i).β * (x i).val * (F i).γ := by
  intro D S N hN r k _ _ _ _ q Y _ _ F hinj hI x hx
  classical
  choose g hgK hgm using fun i => one_place S N hN (q i) (F i) (hI i) (x i) (hx i)
  have hgrp : ∀ i, g i ∈ grpAt S (· = (q i).v) := fun i => (hgK i).1
  have hoff : ∀ i j, j ≠ i → g j ∈ grpOff S (· = (q i).v) := fun i j hji =>
    PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_le_idOff (fun e => hji (hinj e).symm)) (hgrp j)
  refine ⟨(List.ofFn g).prod, ⟨?_, ?_⟩, ?_⟩
  · refine _root_.list_prod_mem fun a ha => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_single_le ⟨j, rfl⟩) (hgrp j)
  · have hlat := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun p => ∃ i, (q i).v = p)).2 S).2.2.2 N
    have hloc : ∀ i, Moves S (List.ofFn g).prod N N (· = (q i).v) := fun i =>
      moves_list_prod _ fun a ha => by
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
        by_cases hji : j = i
        · subst hji; exact (hgK j).2
        · exact moves_off (hoff i j hji)
    intro y hy
    rw [hlat y hN.1, hlat _ hN.1]
    have hy' := PlacesAdeles.supp_mulVec S _ (List.ofFn g).prod hy
    have hey : ∀ v e, e ∈ intAt D (· = v) → ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      simpa [smul_eq_mul] using Ideal.mul_mem_right (y i) _ he.1
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      rw [← Matrix.mulVec_smul]
      exact (hloc i _ (hey _ e he)).1 (h2 _ ⟨i, rfl⟩ e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      have := h2 _ ⟨i, rfl⟩ e he
      rw [← Matrix.mulVec_smul] at this
      exact (hloc i _ (hey _ e he)).2 this
  · intro i
    change locHom S (q i).pr (List.ofFn g).prod = _
    rw [map_list_prod, List.map_ofFn, prod_ofFn_single _ i]
    · exact hgm i
    · intro j hji
      exact map_off (q i) (hoff i j hji)

end GlobalTheory.SplitOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_stabilizer_with_prescribed_splitPlace_matrices : ∀ {D : D7} (S : HSp D) (N : Lat S), IsSelfDualC S N → ∀ {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i)), Function.Injective (fun i => (q i).v) → (∀ i, IntIn (q i) S (F i) N) → ∀ x : (i : Fin r) → GL (Y i) (k i), (∀ i, x i ∈ GlobalTheory.SplitWeil.KO (k i) (Y i)) → ∃ g, InK S N (fun p => ∃ i, (q i).v = p) g ∧ ∀ i, (mt S g).map (q i).pr = (F i).β * (x i).val * (F i).γ := by
  first | exact @GlobalTheory.SplitOnto.exists_of_local | exact GlobalTheory.SplitOnto.exists_of_local | (intros; apply GlobalTheory.SplitOnto.exists_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSmallPf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def ker {A S X : HSp D} (oma : Om A S) (omX : Om S X) (C : WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ℂ :=
  omX (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0

theorem biLift_eq {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ C h₂ = ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) ∂vS.μ := rfl

section

variable {A S X : HSp D} {χA χS χS' χX : (AE D)ˣ →* Circle} {oma : Om A S} {omX : Om S X}

theorem ker_sum {n : ℕ} (C : Fin n → WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX (∑ i, C i) h₀ h₁ h₂ = ∑ i, ker oma omX (C i) h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (∑ i, C i) u v) 0) = ∑ i, fun v => oma (h₀, h₁) (fun u => C i u v) 0 := by
    funext v
    have e : (fun u => (∑ i, C i) u v) = ∑ i, fun u => C i u v := by
      funext u; simp only [Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]; simp only [Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum]; simp only [Finset.sum_apply]

theorem ker_cont (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) :
    Continuous fun x : GA D A × GA D S × GA D X => ker oma omX C x.1 x.2.1 x.2.2 := by
  have := (hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).2.2.2
  exact this.comp (by fun_prop : Continuous fun x : GA D A × GA D S × GA D X =>
    ((x.1, x.2.1), (x.2.1, x.2.2), ((0 : WO A S), (0 : WO S X))))

theorem ker_left (hwa : IsWeilDatumO ψ A S χA χS oma) {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C)
    {γ : GA D A} (hγ : γ ∈ GQ A) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX C (γ * h₀) h₁ h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (γ * h₀, h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((γ * h₀, h₁) : GA D A × GA D S) = (γ, 1) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut γ hγ 1 (one_mem _) _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  rw [e1]

theorem ker_mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {γ : GA D S} (hγ : γ ∈ GQ S) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ (γ * h₁) h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, γ * h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((h₀, γ * h₁) : GA D A × GA D S) = (1, γ) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut 1 (one_mem _) γ hγ _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((γ * h₁, h₂) : GA D S × GA D X) = (γ, 1) * (h₁, h₂) := by simp
  rw [e1, e, map_mul, Module.End.mul_apply, hwX.om_aut γ hγ 1 (one_mem _) _ (hwX.om_pres _ _ hth)]

theorem ker_right (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {δ : GA D X} (hδ : δ ∈ GQ X) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ h₁ (δ * h₂) = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((h₁, δ * h₂) : GA D S × GA D X) = (1, δ) * (h₁, h₂) := by simp
  rw [e, map_mul, Module.End.mul_apply, hwX.om_aut 1 (one_mem _) δ hδ _ (hwX.om_pres _ _ hth)]

theorem inner (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (vA : Vol A) {φ : GA D A → ℂ}
    (hφ : IsContAut A φ) :
    (∀ h₁ h₂, IntegrableOn (fun h₀ => φ h₀ * ker oma omX C h₀ h₁ h₂) vA.𝓕 vA.μ) ∧
      Continuous fun p : GA D S × GA D X => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ p.1 p.2 ∂vA.μ := by
  have hc : Continuous (Function.uncurry fun (g : GA D A) (p : GA D S × GA D X) => φ g * ker oma omX C g p.1 p.2) := by
    show Continuous fun q : GA D A × (GA D S × GA D X) => φ q.1 * ker oma omX C q.1 q.2.1 q.2.2
    exact (hφ.2.comp continuous_fst).mul ((ker_cont hB hwa hwX hC).comp
      (by fun_prop : Continuous fun q : GA D A × (GA D S × GA D X) => (q.1, q.2.1, q.2.2)))
  have H := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D A hA vA (GA D S × GA D X) (fun g p => φ g * ker oma omX C g p.1 p.2) hc
    (fun γ hγ g p => by rw [hφ.1 γ hγ g, ker_left hwa hC hγ])
  exact ⟨fun h₁ h₂ => H.1 (h₁, h₂), H.2.1⟩

theorem mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S)
    {φ : GA D A → ℂ} (hφ : IsContAut A φ) :
    (∀ h₂, IntegrableOn (fun h₁ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) vS.𝓕 vS.μ) ∧
      Continuous fun h₂ => biLift oma omX vA vS φ C h₂ := by
  have H := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS vS (GA D X) (fun h₁ h₂ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ)
    (inner hB hwa hwX hC hA vA hφ).2 (fun γ hγ g p => by simp only [ker_mid hB hwa hwX hC hγ])
  exact ⟨H.1, H.2.1⟩

theorem outer (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) {T L'' : HSp D} (hT : CoCpt T)
    (vA : Vol A) (vS : Vol S) (vT : Vol T) (o'' : OrthDec X T L'') {φ : GA D A → ℂ} (hφ : IsContAut A φ)
    {F : GA D T → ℂ} (hF : IsContAut T F) :
    IntegrableOn (fun h' => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1))) vT.𝓕 vT.μ := by
  have hc := (mid hB hwa hwX hC hA hS vA vS hφ).2
  have hc' : Continuous fun h' : GA D T => biLift oma omX vA vS φ C (o''.emb (h', 1)) :=
    hc.comp (o''.continuous_emb.comp (by fun_prop : Continuous fun h' : GA D T => ((h', 1) : GA D T × GA D L'')))
  refine (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D T hT vT Unit (fun h' _ => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1)))
    ((hF.2.mul hc').comp continuous_fst) (fun γ hγ g _ => ?_)).1 ()
  have e : ((γ * g, 1) : GA D T × GA D L'') = (γ, 1) * (g, 1) := by simp
  have hδ : o''.emb (γ, 1) ∈ GQ X := o''.emb_mem_GQ hγ (one_mem _)
  rw [hF.1 γ hγ g, e, map_mul, biLift_eq, biLift_eq]
  simp only [ker_right hB hwa hwX hC hδ]

theorem biLift_sum (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : IsContAut A φ) {n : ℕ}
    (C : Fin n → WO A S → WO S X → ℂ) (hC : ∀ i, IsBiTheta ψ A S X (C i)) (h₂ : GA D X) :
    biLift oma omX vA vS φ (∑ i, C i) h₂ = ∑ i, biLift oma omX vA vS φ (C i) h₂ := by
  have e1 : ∀ h₁, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (∑ i, C i) h₀ h₁ h₂ ∂vA.μ =
      ∑ i, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (C i) h₀ h₁ h₂ ∂vA.μ := by
    intro h₁
    simp only [ker_sum, Finset.mul_sum]
    exact integral_finsetSum _ fun i _ => (inner hB hwa hwX (hC i) hA vA hφ).1 h₁ h₂
  rw [biLift_eq]
  simp only [e1]
  rw [integral_finsetSum _ fun i _ => (mid hB hwa hwX (hC i) hA hS vA vS hφ).1 h₂]
  rfl

end

theorem seeSmall : ∀ D : D7, SeeSmall D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ hA hS hT χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hTw hz''
    vA vS vT N Ξ Φ₂ hΞΦ φ F hφ hF
  have hB : BiAct D := GlobalTheory.T.seeSawWeilBiAction_commutes D
  have hSL := GlobalTheory.T.lastSeeSaw_thetaIdentity D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX
    hTw hz''
  have hC : ∀ i, IsBiTheta ψ A S X (lastBi o o'' τ (Ξ i) (Φ₂ i)) := fun i =>
    GlobalTheory.T.lastSeeSaw_datum_isTwoVariableThetaFunction D ψ h₁.std V₀ A L S X T L'' o o'' τ hτ (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2
  have e0 : (o.resS S).symm (0, 0) = 0 := by rw [← Prod.zero_eq_mk, map_zero]
  have hpt : ∀ i h', biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) (o''.emb (h', 1)) =
      ∫ h in vS.𝓕, omT (h, h') (Φ₂ i) 0 * liftA o om₁ vA φ (Ξ i) h 0 ∂vS.μ := by
    intro i h'
    rw [biLift_eq]
    congr 1
    funext h
    simp only [liftA, e0]
    rw [← integral_const_mul]
    congr 1
    funext h₀
    have key : oma (h₀, h) (fun u' => omX (h, o''.emb (h', 1)) (lastBi o o'' τ (Ξ i) (Φ₂ i) u') 0) 0 =
        omT (h, h') (Φ₂ i) 0 * om₁ (o.emb (h₀, 1), h) (Ξ i) 0 :=
      ((hSL (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2).2 h₀ h h').symm
    have hk := (hB ψ A S X χA χS χS' (χT * χz⁻¹) oma omX ha hX _ (hC i)).2.2.1 (h₀, h) (h, o''.emb (h', 1)) 0 0
    simp only [ker]
    rw [hk, key]
    ring
  have hsum : ∀ h₂, biLift oma omX vA vS φ (∑ i, lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ =
      ∑ i, biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ := fun h₂ =>
    biLift_sum hB ha hX hA hS vA vS hφ (fun i => lastBi o o'' τ (Ξ i) (Φ₂ i)) hC h₂
  simp only [hsum, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => outer hB ha hX (hC i) hA hS hT vA vS vT o'' hφ hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smallPair, hpt]

end GlobalTheory.SeeSmallPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditiveStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSaw_doubleLift_additive : ∀ D : D7, GlobalTheory.FinPl.SeeSmall D := by
  first | exact @GlobalTheory.SeeSmallPf.seeSmall | exact GlobalTheory.SeeSmallPf.seeSmall | (intros; apply GlobalTheory.SeeSmallPf.seeSmall <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsCombAt
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.CombAt

theorem exists_isCombAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    (Ξ : Matrix Y Y' k → ℂ) : ∃ c : WO S T →₀ ℂ, p.IsCombAt ψ FS FT c Ξ := by
  by_cases h : ∃ Φ : SB (Matrix Y Y' k), Φ.1 = Ξ
  · obtain ⟨Φ, hΦ⟩ := h
    obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
    have hne : O ≠ 0 := by
      rintro rfl
      simp at hO0
    obtain ⟨c, h1, h2⟩ := GlobalTheory.LocComb.exists_comb D k p Y Y' S T FS FT ψ hψ O Φ hne
    refine ⟨c, h1, fun Tm hT Φ₀ Φ' h₀ h' => ?_⟩
    obtain rfl : Φ' = Φ := Subtype.ext (h'.trans hΦ.symm)
    obtain rfl : Φ₀ = O := Subtype.ext (h₀.trans hO.symm)
    exact h2 Tm hT
  · exact ⟨0, by simp, fun Tm _ Φ₀ Φ _ h' => (h ⟨Φ, h'⟩).elim⟩

end GlobalTheory.LocMod.CombAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocPlOff
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.LocPlInhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem exists_latInd (q : GlobalTheory.FinPl.SplitPt D k) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 0 = 1 ∧
      Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem q
  have h1 : {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} =
      (((latO S T M M' fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε q.split.1 heε h).1
    have h3 : q.e • (Witness.upH (ofSplit q) FS FT) x = (ofSplit q).up FS FT x :=
      (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (Witness.up_half (ofSplit q) FS FT x))
    rwa [h3] at h2
  rw [h1]
  have ho := Witness.lat_open (ofSplit q) FS FT hS hT
  have hk := Witness.lat_compact (ofSplit q) FS FT hS hT
  generalize ((latO S T _ _ fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) = A at ho hk
  have hcl : IsClopen (A : Set (Matrix Y Y' k)) := ⟨A.isClosed_of_isOpen ho, ho⟩
  exact ⟨⟨(A : Set (Matrix Y Y' k)).indicator 1, (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
      HasCompactSupport.intro hk fun x hx => Set.indicator_of_notMem hx _⟩, Set.indicator_of_mem A.zero_mem _, rfl⟩


end GlobalTheory.SeeSaw.LocPlInhab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StdSteps

theorem even_N (R : Ranks) (j : ℕ) : Even (R.N j) :=
  R.k_even.add (R.t_odd.add_one.mul_left j)

theorem N_lt_succ (R : Ranks) (j : ℕ) : R.N j < R.N (j + 1) := by
  unfold Ranks.N
  rw [Nat.add_mul]
  omega

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (D : D7) (h : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  rw [Host.xi0, h, Ideal.absNorm_top, map_div₀, map_neg, map_one, map_mul, h1, Nat.cast_one, map_one, one_mul, Complex.ofReal_inv]
  field_simp
  rw [Complex.I_sq]

theorem scale_eq (D : D7) {δ : ℂ} (hδ : δ ≠ 0) :
    (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D ⊤ δ))⁻¹ * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹ := by
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ‖δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
  rw [GlobalTheory.MomDict.area_lamOf D ⊤ δ top_ne_bot, Ideal.absNorm_top, Complex.normSq_eq_norm_sq]
  field_simp
  simp

end GlobalTheory.AdForm.StdSteps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_iff_of_carries (y k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : Submodule (𝓞 E) (Fin n → E))
    (hN : Submodule.IsFullLattice E N) (h1 : Formalism.L2.Herm.Carries (y * k) (Formalism.L2.Col.stdLat E n) N)
    (h2 : Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (x : Fin n → E) :
    x ∈ N ↔ ∀ i, (((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) i ∈ Formalism.L2.Herm.intAf F E := by
  have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.mpr hN.fg) hN.span_eq_top
  have e0 : x ∈ N ↔ (fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) ∈ Formalism.L2.Herm.hatL (F := F) N := by
    conv_lhs => rw [← hone]
    show (((1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N ↔ _
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  rw [e0, h1, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← h2]
  exact Formalism.L2.Col.mem_latS_std _

theorem finM_mul' {D : D7} (V : HSp D) {m : ℕ} (hn : V.rank = m) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  change (Formalism.L2.Theta.mt V (g * h)).map (toEAf D) = (Formalism.L2.Theta.mt V g).map (toEAf D) * (Formalism.L2.Theta.mt V h).map (toEAf D)
  rw [← Matrix.map_mul]
  congr 1

theorem finM_one' {D : D7} (V : HSp D) {m : ℕ} (hn : V.rank = m) : finM V hn 1 = 1 := by
  subst hn
  change (Formalism.L2.Theta.mt V 1).map (toEAf D) = 1
  have e : Formalism.L2.Theta.mt V 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one]
    rfl
  rw [e, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RepLattice

namespace GlobalTheory.RepLattice
open GlobalTheory.AdForm

end GlobalTheory.RepLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocMod.GValProof

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_frame {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) : Fintype.card Y = N := by
  apply le_antisymm
  · calc Fintype.card Y = (F.γ * F.β).rank := by rw [F.γβ, Matrix.rank_one]
      _ ≤ F.β.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin N) := Matrix.rank_le_card_height _
      _ = N := Fintype.card_fin N
  · calc N = Fintype.card (Fin N) := (Fintype.card_fin N).symm
      _ = (F.β * F.γ).rank := by rw [F.βγ, Matrix.rank_one]
      _ ≤ F.γ.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card Y := Matrix.rank_le_card_height _

theorem core_of_bes (p : Place D k) {ρ : ℕ} (B : BesLev D ρ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (G : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA G) :
    ∃ F₀ : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F₀ := by
  obtain ⟨hc, hA, -, hz, -⟩ := h
  let f : D.host.E →+* k := p.π.comp (incA D)
  have hpr : ∀ a, p.pr a = f a := fun _ => rfl
  let e : n ⊕ Unit → n ⊕ Fin c := Sum.elim Sum.inl fun _ => Sum.inr ⟨ρ, by omega⟩
  have he : Function.Injective e := by
    rintro (a | ⟨⟩) (b | ⟨⟩) hab <;> simp_all [e]
  let βA : Matrix (Fin B.V₀.rank) n k := B.o.iA.map p.pr * FA.β
  let β : Matrix (Fin B.V₀.rank) (n ⊕ Unit) k :=
    Matrix.of fun r y => Sum.elim (fun a => βA r a) (fun _ => s * p.pr (vecB B.o B.ζ r)) y
  let I : Matrix (Fin B.V.rank) (Fin B.V₀.rank) k := B.d.i₀.map p.pr
  have hmap : I * B.o.iA.map p.pr = (B.d.i₀ * B.o.iA).map p.pr := (Matrix.map_mul (f := f)).symm
  have hIβ : I * β = G.β.submatrix id e := by
    ext r (a | ⟨⟩)
    · simp only [submatrix_apply, id, e, Sum.elim_inl]
      rw [hA]
      have : (I * β) r (Sum.inl a) = (I * βA) r a := by
        simp only [Matrix.mul_apply, β, Matrix.of_apply, Sum.elim_inl]
      rw [this, ← Matrix.mul_assoc, hmap]
    · simp only [submatrix_apply, id, e, Sum.elim_inr]
      rw [hz ⟨ρ, by omega⟩ rfl r, hpr, RingHom.map_mulVec]
      simp only [Matrix.mul_apply, β, Matrix.of_apply, Sum.elim_inr, mulVec, dotProduct, Finset.mul_sum, I,
        Function.comp_apply, hpr]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.map_apply, hpr]
      ring
  let γ : Matrix (n ⊕ Unit) (Fin B.V₀.rank) k := G.γ.submatrix e id * I
  have hγβ : γ * β = 1 := by
    rw [Matrix.mul_assoc, hIβ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, G.γβ, Matrix.submatrix_one _ he]
  have hcard : Fintype.card (n ⊕ Unit) = B.V₀.rank := by
    have h1 := card_frame G
    have h2 := B.d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1 ⊢
    omega
  have hβγ : β * γ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hcard)).1 hγβ
  exact ⟨⟨β, γ, hβγ, hγβ⟩, fun r a => rfl, fun r => rfl⟩

theorem hz_link (p : Place D k) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) :
    p.hz B = -p.xi ^ 2 * p.hz B' := by
  let f : D.host.E →+* k := p.π.comp (incA D)
  have hpr : ∀ a, p.pr a = f a := fun _ => rfl
  rw [Place.hz, Place.hz, Place.xi, l.norm, hpr, hpr, hpr, map_mul, map_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]
  ring

theorem cont_of_cond (ψ : AddChar k Circle) (h : HasConductor ψ 1) : Continuous ψ := h.continuous

theorem one_mem_SB (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] :
    (Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => (1 : ℂ)) ∈ SB (Matrix n n' k) := by
  set S : Set (Matrix n n' k) := {x | ∀ r q, x r q ∈ 𝒪[k]} with hSdef
  have hS : (S : Set (n → n' → k)) = Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h r _ q _ => h r q, fun h r q => h r (Set.mem_univ _) q (Set.mem_univ _)⟩
  have hO : IsOpen S := by
    change IsOpen (S : Set (n → n' → k))
    rw [hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      Valuation.isOpen_integer (v := valuation k)
  have hK : IsCompact S := by
    change IsCompact (S : Set (n → n' → k))
    rw [hS]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => by simp [Set.indicator, hx]⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ S
  · exact ⟨S, hO, hx, fun y hy => by simp [Set.indicator, hy, hx]⟩
  · exact ⟨Sᶜ, hK.isClosed.isOpen_compl, hx, fun y hy => by
      have hy' : y ∉ S := hy
      simp [Set.indicator, hy', hx]⟩

theorem sliceCol_mem {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {f : Matrix n (n' ⊕ Unit) k → ℂ}
    (hf : f ∈ SB _) : (fun a : Matrix n n' k => f (fromCols a 0)) ∈ SB _ := by
  have hc : Continuous fun a : Matrix n n' k => fromCols a (0 : Matrix n Unit k) := by
    refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · simp only [fromCols_apply_inl]; exact continuous_id.matrix_elem i j
    · simp only [fromCols_apply_inr]; exact continuous_const
  have hd : Continuous fun x : Matrix n (n' ⊕ Unit) k => x.toCols₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)
  refine ⟨hf.1.comp_continuous hc, HasCompactSupport.intro (hf.2.isCompact.image hd) fun a ha => ?_⟩
  by_contra h0
  exact ha ⟨fromCols a 0, subset_tsupport _ h0, toCols₁_fromCols _ _⟩

theorem sliceRow_mem {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {f : Matrix (n ⊕ Unit) n' k → ℂ}
    (hf : f ∈ SB _) : (fun a : Matrix n n' k => f (fromRows a 0)) ∈ SB _ := by
  have hc : Continuous fun a : Matrix n n' k => fromRows a (0 : Matrix Unit n' k) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · simp only [fromRows_apply_inl]; exact continuous_id.matrix_elem i j
    · simp only [fromRows_apply_inr]; exact continuous_const
  have hd : Continuous fun x : Matrix (n ⊕ Unit) n' k => x.toRows₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem (Sum.inl i) j
  refine ⟨hf.1.comp_continuous hc, HasCompactSupport.intro (hf.2.isCompact.image hd) fun a ha => ?_⟩
  by_contra h0
  exact ha ⟨fromRows a 0, subset_tsupport _ h0, toRows₁_fromRows _ _⟩
end

theorem gval : ∀ (D : D7), FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (c₁ : WO B.A J.W₀ →₀ ℂ) (c₂ : WO J.W₀ B'.A →₀ ℂ),
    p.IsCombAt ψ F.F₀ F.F₁ c₁ ((S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1) →
    p.IsCombAt ψ F.F₁ F.F₂ c₂ ((S.T t).entry S.ψ ν (j + 1) c H 1 1) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂,
    Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) → Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) → IsOne O₁ → IsOne O₂ →
    GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (T₂ Φ₂)) =
      C • biComb ψ B.A J.W₀ B'.A c₁ c₂ (GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ O₁)) (flatFB s₂ (T₂ O₂))) := by
  intro D hBF hFB hCL hSym k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hstd hchar j c H
  by_cases hc : ∃ r, c = 2 * r
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro σ B J B' F
    exact absurd ⟨σ, by have := F.bes.1; omega⟩ hc
  obtain ⟨r, hr⟩ := hc
  obtain ⟨-, hPC, hPR, hDS⟩ := hSym k ν hν s κ S t
  obtain ⟨-, C, hC, hval⟩ := hDS j c H r hr
  refine ⟨(C : ℂ), by exact_mod_cast hC.ne', ?_⟩
  intro σ B J B' F s₁ s₂ l vL c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hΦ₁ hΦ₂ hO₁ hO₂
  have hσ : σ = r := by have := F.bes.1; omega
  subst hσ
  have hψc : Continuous S.ψ := cont_of_cond S.ψ S.cond
  obtain ⟨C₀, hC₀⟩ := core_of_bes p B F.s F.F₀ F.G₀ F.bes
  obtain ⟨C₂, hC₂⟩ := core_of_bes p B' (F.s * p.xi) F.F₂ F.G₂ F.bes'
  have hjac : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := by
    rw [← hz_link p B B' l]; exact F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF k p ν hν.1 ψ S.ψ hchar (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁ hC₀ F.bes F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB k p ν hν.1 ψ S.ψ hchar σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂ hjac hC₂ F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL k p ν hν.1 ψ hstd S.ψ hchar (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hfl := GlobalTheory.LocFlat.flat_SB_onto k S.ψ ν hψc hν.1
  have m₁ := fun Φ : SB _ => ((hfl (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 Φ.1 Φ.2
  have m₂ := fun Φ : SB _ => ((hfl (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) (c + 1) (σ + 1) (by omega)).2 (by omega)).1 Φ.1 Φ.2
  let Ψ₁ : SB _ := ⟨_, m₁ Φ₁⟩
  let Ψ₂ : SB _ := ⟨_, m₂ Φ₂⟩
  let P₁ : SB _ := ⟨_, m₁ O₁⟩
  let P₂ : SB _ := ⟨_, m₂ O₂⟩
  rw [hU₁e Φ₁ Ψ₁ rfl, hU₂e Φ₂ Ψ₂ rfl, hU₁e O₁ P₁ rfl, hU₂e O₂ P₂ rfl]
  obtain ⟨Ξ, hΞ, e1⟩ := hΛe Ψ₁ Ψ₂
  obtain ⟨ΞO, hΞO, e2⟩ := hΛe P₁ P₂
  rw [e1, e2]

  have hE₁ : (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 ∈ SB _ := by
    obtain ⟨C', hC', hpc⟩ := hPC j (c + 1) (by omega) (σ + 1) (by omega)
    have hs := sliceCol_mem Ψ₁.2
    have e : (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 = (C'⁻¹ : ℂ) • fun a => Ψ₁.1 (fromCols a 0) := by
      funext a
      simp only [Ψ₁, Pi.smul_apply, smul_eq_mul]
      rw [hΦ₁, hpc]
      have hC'0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'.ne'
      simp only [toCols₁_fromCols, fromCols_apply_inr, Matrix.zero_apply]
      have hz : (fun _ => (0 : k)) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (σ + 1))⁻¹ := (box _ _).zero_mem
      simp only [hz, if_true, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ hC'0, one_mul]
    rw [e]; exact (SB _).smul_mem _ hs
  have hE₂ : (S.T t).entry S.ψ ν (j + 1) c H 1 1 ∈ SB _ := by
    obtain ⟨C', hC', hpr⟩ := hPR (j + 1) c H σ hr
    have hs := sliceRow_mem Ψ₂.2
    have e : (S.T t).entry S.ψ ν (j + 1) c H 1 1 = (C'⁻¹ : ℂ) • fun a => Ψ₂.1 (fromRows a 0) := by
      funext a
      simp only [Ψ₂, Pi.smul_apply, smul_eq_mul]
      rw [hΦ₂, hpr]
      have hC'0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'.ne'
      simp only [toRows₁_fromRows, fromRows_apply_inr, Matrix.zero_apply]
      have hz : a.fromRows (0 : Matrix Unit (XIx (Fin κ) t (j + 1)) k) (Sum.inr ()) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (σ + 1)) := (box _ _).zero_mem
      simp only [hz, if_true, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ hC'0, one_mul]
    rw [e]; exact (SB _).smul_mem _ hs
  let E₁ : SB _ := ⟨_, hE₁⟩
  let E₂ : SB _ := ⟨_, hE₂⟩
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hΞ' : ∀ q, ((C : ℂ)⁻¹ • Ξ).1 q = E₁.1 q.1 * E₂.1 q.2 := by
    intro q
    rw [Submodule.coe_smul, Pi.smul_apply, hΞ]
    simp only [Ψ₁, Ψ₂, E₁, E₂]
    rw [hΦ₁, hΦ₂, hval q, smul_eq_mul]
    field_simp
  have hΞe : Ξ = (C : ℂ) • ((C : ℂ)⁻¹ • Ξ) := by rw [smul_smul, mul_inv_cancel₀ hCne, one_smul]

  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator k S.ψ ν S.cond hν
  let Q₁ : SB (Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k) := ⟨_, one_mem_SB _ _⟩
  let Q₂ : SB (Matrix (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) k) := ⟨_, one_mem_SB _ _⟩
  have hP₁ : P₁.1 = Set.indicator {x : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
    simp only [P₁]
    rw [hO₁, (hun (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (XIx (Fin κ) t j) (c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)]
  have hP₂ : P₂.1 = Set.indicator {x : Matrix (XIx (Fin κ) t (j + 1 + 1) ⊕ Unit) (XIx (Fin κ) t (j + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
    simp only [P₂]
    rw [hO₂, (hun (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1) (σ + 1)).2.1 (by omega) (by omega)]
  have hΞO' : ∀ q, ΞO.1 q = Q₁.1 q.1 * Q₂.1 q.2 := by
    intro q
    rw [hΞO, hP₁, hP₂]
    exact (hun (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1 + 1)) 0 0).2.2 q
  have hbi := (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ _ _ _).1 B.A J.W₀ B'.A F.F₀ F.F₁ F.F₂ Λ c₁ c₂ E₁ Q₁ E₂ Q₂ ((C : ℂ)⁻¹ • Ξ) ΞO hΛ hc₁ hc₂ rfl rfl hΞ' hΞO'
  rw [hΞe, map_smul, hbi]

theorem gval_of_laws : ∀ (D : D7), FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse → GVal D := by
  intro D hBF hFB hCL hSym k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hchar j c H
  by_cases hstd : IsStdChar D ψ (-1)
  · exact gval D hBF hFB hCL hSym k ν hν p s κ S t ψ hstd hchar j c H
  · refine ⟨1, one_ne_zero, ?_⟩
    intro σ B J B' F s₁
    exact absurd s₁.weil.std hstd

end GlobalTheory.LocMod.GValProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitDatumCompletedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitDatumCompletedLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SBHalfAt

theorem isSBHalf_extFun_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k),
      IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
        (extFun α β Ψ) := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β LS LT hS hT Ψ hΨ
  exact GlobalTheory.FinPl.CombProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ

end GlobalTheory.FinPl.SBHalfAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitDatumCompletedLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_split_datum_completed_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k),
      IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
        (extFun α β Ψ) := by
  first | exact @GlobalTheory.FinPl.SBHalfAt.isSBHalf_extFun_latO | exact GlobalTheory.FinPl.SBHalfAt.isSBHalf_extFun_latO | (intros; apply GlobalTheory.FinPl.SBHalfAt.isSBHalf_extFun_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

noncomputable section
namespace GlobalTheory.HaarR

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def prodR (p : ℕ) (q : GL n k × N k n c p) : R k n c p :=
  ⟨embX c q.1 * (q.2 : GL (n ⊕ Fin c) k), mul_mem (Subgroup.mem_sup_left ⟨q.1, rfl⟩) (Subgroup.mem_sup_right q.2.2)⟩

def prodRFJ (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) : RFJ k n c ρ :=
  ⟨embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2,
    mul_mem (Subgroup.mem_sup_right (mul_mem (Subgroup.mem_sup_left ⟨q.1.1, rfl⟩) (Subgroup.mem_sup_right q.1.2.2)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c ρ).2.2.2.2.2.2.2 (ρ + 1) q.2 (Nat.lt_succ_self ρ)).1))⟩

@[simp] theorem prodR_coe (p : ℕ) (q : GL n k × N k n c p) :
    (prodR p q : GL (n ⊕ Fin c) k) = embX c q.1 * (q.2 : GL (n ⊕ Fin c) k) := rfl

@[simp] theorem prodRFJ_coe (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    (prodRFJ ρ q : GL (n ⊕ Fin c) k) = embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2 := rfl

def cjE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) : N k n c (ρ + 1) :=
  ⟨colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹,
    (GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ h1 h2).2 β u u.2⟩

@[simp] theorem cjE_coe (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) :
    (cjE ρ h1 h2 β u : GL (n ⊕ Fin c) k) = colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹ := rfl

end GlobalTheory.HaarR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QuotientFiniteLevel

variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}

def locK (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) : Subgroup (GA D (c.V (j + 1))) :=
  ((F.Q i).T.lev (j + 1) ((F.Q i).s - j) (by have := (F.Q i).hs; omega)).J.map
    ((F.Q i).gl (j + 1) ((F.Q i).s - j) (by have := (F.Q i).hs; omega))

def qK (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) : Subgroup (GA D (c.V (j + 1))) :=
  ⨆ i, locK F j σ h i

end GlobalTheory.QuotientFiniteLevel
end
end
