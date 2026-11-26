module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AllBij

section Comb

variable {G : Type} [Group G]

def act (c : G →₀ ℂ) (F : G → ℂ) : G → ℂ := c.sum fun g x => x • rTrans g F

theorem act_apply (c : G →₀ ℂ) (F : G → ℂ) (y : G) : act c F y = c.sum fun g x => x * F (y * g) := by
  simp [act, Finsupp.sum, Finset.sum_apply, rTrans]

def cmul (c d : G →₀ ℂ) : G →₀ ℂ := c.sum fun g x => d.sum fun h y => Finsupp.single (g * h) (x * y)

theorem act_cmul (c d : G →₀ ℂ) (F : G → ℂ) : act (cmul c d) F = act c (act d F) := by
  funext y
  rw [act_apply, act_apply, cmul, Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul]), act_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  simp [mul_assoc]

theorem act_single_one (F : G → ℂ) : act (Finsupp.single 1 1) F = F := by
  funext y; rw [act_apply, Finsupp.sum_single_index (by simp)]; simp

theorem act_mapDomain {H : Type} (f : H → G) (c : H →₀ ℂ) (F : G → ℂ) :
    act (Finsupp.mapDomain f c) F = c.sum fun h x => x • rTrans (f h) F := by
  rw [act, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]

theorem cmul_mem {S : Subgroup G} {c d : G →₀ ℂ} (hc : ∀ g, c g ≠ 0 → g ∈ S) (hd : ∀ g, d g ≠ 0 → g ∈ S) :
    ∀ g, cmul c d g ≠ 0 → g ∈ S := by
  classical
  intro g hg
  obtain ⟨a, ha, hga⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum (Finsupp.mem_support_iff.2 hg))
  obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hga)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hgb)]
  exact S.mul_mem (hc a (Finsupp.mem_support_iff.1 ha)) (hd b (Finsupp.mem_support_iff.1 hb))

theorem mapDomain_mem {H : Type} {S : Subgroup G} (f : H → G) (hf : ∀ h, f h ∈ S) (c : H →₀ ℂ) :
    ∀ g, Finsupp.mapDomain f c g ≠ 0 → g ∈ S := by
  classical
  intro g hg
  obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 hg))
  exact hf h

def actL (c : G →₀ ℂ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := act c
  map_add' F F' := by funext y; simp [act_apply, mul_add, Finsupp.sum_add]
  map_smul' r F := by funext y; simp [act_apply, Finsupp.mul_sum, mul_left_comm]

end Comb

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7}

theorem isContAut_act {V : HSp D} (c : GA D V →₀ ℂ) {F : GA D V → ℂ} (hF : IsContAut V F) : IsContAut V (act c F) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · rw [act_apply, act_apply]
    exact Finsupp.sum_congr fun h _ => by rw [mul_assoc, hF.1 γ hγ]
  · have : act c F = fun y => c.sum fun g x => x * F (y * g) := funext (act_apply c F)
    rw [this]
    exact continuous_finsetSum _ fun h _ => continuous_const.mul (hF.2.comp (continuous_id.mul continuous_const))

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem rep_eq (β : Frame p S n) (g : GL n k) (F : GA D S → ℂ) : β.rep g F = rTrans (β.gl g) F := rfl

theorem sum_rep_eq (β : Frame p S n) (c : GL n k →₀ ℂ) (F : GA D S → ℂ) :
    (c.sum fun g a => a • β.rep g F) = act (Finsupp.mapDomain β.gl c) F := by
  rw [act_mapDomain]; rfl

theorem ramAt_act (β : Frame p S n) (P : Pair k n) (c : GA D S →₀ ℂ)
    (hc : ∀ x, c x ≠ 0 → ∀ g, x * β.gl g = β.gl g * x) {φ₀ : GA D S → ℂ} (hφ : RamAt β P φ₀) :
    RamAt β P (act c φ₀) := by
  obtain ⟨φ, ⟨heq, hram, hcont⟩, rfl⟩ := hφ
  refine ⟨fun Q => actL c (φ Q), ⟨?_, ?_, fun Q => isContAut_act c (hcont Q)⟩, rfl⟩
  · intro g Q
    show act c (φ (g • Q)) = β.rep g (act c (φ Q))
    rw [heq g Q]
    funext y
    rw [rep_eq, rep_eq, act_apply]
    show _ = act c (φ Q) (y * β.gl g)
    rw [act_apply]
    refine Finsupp.sum_congr fun x hx => ?_
    simp only [rTrans]
    rw [mul_assoc, hc x (Finsupp.mem_support_iff.1 hx) g, mul_assoc]
  · let _ := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun Q => ?_
    have h0 := (mem_Mram φ).1 hram Q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h0, map_zero]

end Frames

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7}

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  simp only [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  have key : ∀ x : GL (Fin V.rank) (AE D), Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) x =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor h) (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) x) := by
    intro x; ext i j; simp [Ideal.Quotient.factor_mk]
  rw [key, hg, map_one]

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem idAt_le_idOff {v w : Pl D} (h : v ≠ w) : idAt D (· = v) ≤ idOff D (· = w) := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = w := u.2
  exact ha.2 ⟨u.1, fun e => h (e.symm.trans hu)⟩

theorem grpAt_comm (V : HSp D) {v w : Pl D} (h : v ≠ w) {x y : GA D V} (hx : x ∈ grpAt V (· = w))
    (hy : y ∈ grpAt V (· = v)) : x * y = y * x :=
  (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = w)).2 V |>.2.1 x hx y (congGrp_mono V (idAt_le_idOff h) hy)

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {A S : HSp D}

theorem gl_mem {p₀ : SplitPt D k} (β : Frame p₀ A n) (g : GL n k) : β.gl g ∈ grpAt A (· = p₀.v) :=
  ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k p₀ A n β).1 _).2 ⟨g, rfl⟩

theorem sAll_cons (a : PairDat p A S n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (ε : ι → 𝓀[k]ˣ) (i : ι) (l : List ι) :
    a.sAll q χ ε (i :: l) = sOp (a.α i) (a.P i) q (χ i) (ε i) ∘ a.sAll q χ ε l := rfl

theorem place (a : PairDat p A S n) (hinj : Function.Injective fun i => (p i).v) (q : Unif k)
    (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (i : ι) :
    (∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 → g ∈ grpAt A (· = (p i).v)) ∧ (∀ g, c' g ≠ 0 → g ∈ grpAt A (· = (p i).v)) ∧
      (∀ φ, sOp (a.α i) (a.P i) q (resChar χ hχ q) ε φ = act c φ) ∧
      ∀ φ, a.Ram φ → a.Ram (act c' φ) ∧ sOp (a.α i) (a.P i) q (resChar χ hχ q) ε (act c' φ) = φ) ∧
    Set.MapsTo (sOp (a.α i) (a.P i) q (resChar χ hχ q) ε) {φ | a.Ram φ} {φ | a.Ram φ} ∧
    Set.InjOn (sOp (a.α i) (a.P i) q (resChar χ hχ q) ε) {φ | a.Ram φ} := by
  obtain ⟨hbij, -, c, c', hc, hc'⟩ := GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n q χ hχ _ rfl ε A (a.α i) (a.P i)
  have hC := mapDomain_mem _ (gl_mem (a.α i)) c
  have hC' := mapDomain_mem _ (gl_mem (a.α i)) c'
  have hT : ∀ φ, sOp (a.α i) (a.P i) q (resChar χ hχ q) ε φ = act (Finsupp.mapDomain (a.α i).gl c) φ :=
    fun φ => (hc φ).trans (sum_rep_eq _ _ _)
  have other : ∀ C₀ : GA D A →₀ ℂ, (∀ g, C₀ g ≠ 0 → g ∈ grpAt A (· = (p i).v)) → ∀ j, j ≠ i → ∀ φ,
      RamAt (a.α j) (a.P j) φ → RamAt (a.α j) (a.P j) (act C₀ φ) := fun C₀ hC₀ j hj φ hφ =>
    ramAt_act _ _ C₀ (fun x hx g => grpAt_comm A (fun e => hj (hinj e)) (hC₀ x hx) (gl_mem _ g)) hφ
  refine ⟨⟨_, _, hC, hC', hT, fun φ hφ => ?_⟩, fun φ hφ => ⟨?_, fun j => ?_⟩, hbij.injOn.mono fun φ hφ => hφ.2 i⟩
  · obtain ⟨h1, h2⟩ := hc' φ (hφ.2 i)
    rw [sum_rep_eq] at h1 h2
    refine ⟨⟨isContAut_act _ hφ.1, fun j => ?_⟩, h1⟩
    rcases eq_or_ne j i with rfl | hj
    · exact h2
    · exact other _ hC' j hj φ (hφ.2 j)
  · rw [hT]; exact isContAut_act _ hφ.1
  · rcases eq_or_ne j i with rfl | hj
    · exact hbij.mapsTo (hφ.2 j)
    · rw [hT]; exact other _ hC j hj φ (hφ.2 j)

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl


open AllBij in
theorem allBijective_all : ∀ D : D7, AllBijective D := by
  intro D k _ _ _ _ ι p q χ hχ ε n _ _ A S a hinj I
  have hsub : ∀ i, grpAt A (· = (p i).v) ≤ grpAt A fun v => ∃ i, v = (p i).v :=
    fun i => congGrp_mono A (idAt_mono fun v hv => ⟨i, hv⟩)
  have key : ∀ I : List ι, Set.MapsTo (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} {φ | a.Ram φ} ∧
      Set.InjOn (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} ∧
      ∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ g, c' g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ φ, a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ = act c φ) ∧
        ∀ φ, a.Ram φ → a.Ram (act c' φ) ∧ a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I (act c' φ) = φ := by
    intro I
    induction I with
    | nil =>
      have h1 : ∀ g, (Finsupp.single (1 : GA D A) (1 : ℂ)) g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v :=
        fun g h => by rw [(Finsupp.single_apply_ne_zero.1 h).1]; exact Subgroup.one_mem _
      refine ⟨fun φ h => h, fun φ _ ψ _ h => h, _, _, h1, h1, fun φ => (act_single_one φ).symm, fun φ h => ?_⟩
      rw [act_single_one]; exact ⟨h, rfl⟩
    | cons i l ih =>
      obtain ⟨⟨C, C', hC, hC', hT, hinv⟩, maps, inj⟩ := place a hinj q (χ i) (hχ i) (ε i) i
      obtain ⟨mapsl, injl, c, c', hc, hc', hl, hinvl⟩ := ih
      rw [sAll_cons]
      refine ⟨maps.comp mapsl, inj.comp injl mapsl, cmul C c, cmul c' C', cmul_mem (fun g h => hsub i (hC g h)) hc,
        cmul_mem hc' (fun g h => hsub i (hC' g h)), fun φ => ?_, fun φ hφ => ?_⟩
      · rw [act_cmul, ← hl, Function.comp_apply, hT]
      · rw [act_cmul]
        obtain ⟨h1, h2⟩ := hinv φ hφ
        obtain ⟨h3, h4⟩ := hinvl _ h1
        refine ⟨h3, ?_⟩
        rw [Function.comp_apply, h4, h2]
  obtain ⟨maps, inj, c, c', hc, hc', hT, hinv⟩ := key I
  exact ⟨⟨maps, inj, fun φ hφ => ⟨act c' φ, (hinv φ hφ).1, (hinv φ hφ).2⟩⟩, c, c',
    fun g h => h.elim (hc g) (hc' g), hT, hinv⟩

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlacesStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces : ∀ D : D7, GlobalTheory.FinPl.AllBijective D := by
  first | exact @GlobalTheory.FinPl.allBijective_all | exact GlobalTheory.FinPl.allBijective_all | (intros; apply GlobalTheory.FinPl.allBijective_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorHomSelfDualComponentsSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorHomSelfDualComponentsSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem isLattice_of_isLat_selfDual {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p S n) (L : Lat S) (hL : IsSelfDualC S L) (Λ : Submodule 𝒪[k] (n → k)) (h : β.IsLat L Λ) :
    Λ.IsFullLattice k := by
  obtain ⟨Λ₀, h₀, hI, -⟩ := (GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β).2.2.2.1 L hL
  have e : Λ = Λ₀ := Submodule.ext fun x => (h x).trans (hI x).symm
  have hlat : Λ.IsLattice k := e ▸ h₀
  refine { toIsLattice := hlat, span_eq_top := eq_top_iff.mpr fun x _ => ?_ }
  obtain ⟨m, s, c, hs, hc, -⟩ := GlobalTheory.FinPl.FrameLat.exists_gen (p := p) hL
  have hx := congrArg (β.b' *ᵥ ·) (hc (β.b *ᵥ x))
  simp only [Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec, Matrix.mulVec_sum,
    Matrix.mulVec_smul] at hx
  rw [hx]
  refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  apply (h _).2
  rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
  exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (p := p) (hs l)

theorem latInd_mem_SB_of_selfDual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → latInd ΛS ΛT ∈ SB (Matrix n n' k) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT ΛS ΛT hα hβ
  have := isLattice_of_isLat_selfDual α LS hS ΛS hα
  have := isLattice_of_isLat_selfDual β LT hT ΛT hβ
  exact GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT

end GlobalTheory.FinPl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorHomSelfDualComponentsSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_hom_selfDual_components_schwartzBruhat : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → latInd ΛS ΛT ∈ SB (Matrix n n' k) := by
  first | exact @GlobalTheory.FinPl.latInd_mem_SB_of_selfDual | exact GlobalTheory.FinPl.latInd_mem_SB_of_selfDual | (intros; apply GlobalTheory.FinPl.latInd_mem_SB_of_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSobolevBoundThetaPointwise
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSobolevBoundThetaPointwise
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDensSup

theorem sup_le_sobO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ w, ‖f w‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU
  haveI : LocallyCompactSpace (WO S T) := (GlobalTheory.MixModel.lattice_Mx D T.rank S.rank).2.1
  obtain ⟨K₀, hK₀n, hK₀U, hK₀c⟩ := local_compact_nhds (hU.mem_nhds U.zero_mem)
  obtain ⟨C, hC⟩ := GlobalTheory.LevelSupBound.pointwise (S := S) (T := T) hψ hθ hK₀n hK₀c
  refine ⟨Module.finrank ℝ (GlobalTheory.FockCompare.RW T S), C, fun f hf w => ?_⟩
  have h := hC μ 𝓕 hm 1 one_pos f hf.1 (fun u hu hinf => by rw [one_smul]; exact hf.2 u (hK₀U hu) hinf) w
  refine h.trans (le_of_eq ?_)
  congr 1
  simp

end GlobalTheory.ThetaDensSup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSobolevBoundThetaPointwiseStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sobolev_bound_theta_pointwise : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ w, ‖f w‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f := by
  first | exact @GlobalTheory.ThetaDensSup.sup_le_sobO | exact GlobalTheory.ThetaDensSup.sup_le_sobO | (intros; apply GlobalTheory.ThetaDensSup.sup_le_sobO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelSobolevBoundWeilCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelSobolevBoundWeilCompact
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDens.WeilCompact

variable {D : D7}

theorem mt_mul_eq (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one_eq (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem continuous_mt_eq (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ x) = x := by
  unfold Formalism.IndefR.Datum.actO
  rw [inv_inv]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.Theta.mt T h), ← mt_mul_eq, ← mt_mul_eq, mul_inv_cancel, mul_inv_cancel,
    mt_one_eq, mt_one_eq, Matrix.one_mul, Matrix.mul_one]


open GlobalTheory.Size in
theorem dRho_om {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (g : GA D S) (h : GA D T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ
        (compAt θ τ (Formalism.L2.Theta.mt T h⁻¹) * z * compAt θ τ (Formalism.L2.Theta.mt S g)) f) := by
  rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ _ hf]
  congr 1
  have e1 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h
  have e2 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g
  simp only [Matrix.mul_assoc]
  rw [e2, Matrix.mul_one, ← Matrix.mul_assoc, e1, Matrix.one_mul]

def dirSize (θ : InfFam D) (S T : HSp D) (x : GA D S × GA D T) : ℝ :=
  ∑ a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, ∑ i, ∑ j,
    (|((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).re| +
     |((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).im|)

theorem continuous_dirSize {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) : Continuous (dirSize θ S T) := by
  unfold dirSize
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq T).comp continuous_snd.inv)
  have h2 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt S x.1) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq S).comp continuous_fst)
  have h3 := ((h1.matrix_mul (continuous_const (y := Matrix.single a.2.1 a.2.2.1
    (if a.2.2.2 then Complex.I else 1)))).matrix_mul h2).matrix_elem i j
  exact (continuous_abs.comp (Complex.continuous_re.comp h3)).add (continuous_abs.comp (Complex.continuous_im.comp h3))

theorem actO_add' {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (x + y) = Formalism.IndefR.Datum.actO S T g h x + Formalism.IndefR.Datum.actO S T g h y := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_zero' {S T : HSp D} (g : GA D S) (h : GA D T) : Formalism.IndefR.Datum.actO S T g h 0 = 0 := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_zero, Matrix.zero_mul]

theorem actO_neg' {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (-x) = -Formalism.IndefR.Datum.actO S T g h x := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_neg, Matrix.neg_mul]


open GlobalTheory.Size in
theorem word_om_le {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {K : Set (GA D S × GA D T)}
    (B : ℝ≥0) (hB : ∀ x ∈ K, dirSize θ S T x ≤ B) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), l.length = k → ∀ x ∈ K,
      ∀ g, IsThetaFunO ψ S T g → l2O μ 𝓕 (wordAct (heisDer ψ θ) l (om x g)) ≤ C * sobO ψ θ μ 𝓕 k g := by
  induction k with
  | zero =>
    refine ⟨1, fun l hl x _ g hg => ?_⟩
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    rw [wordAct_nil, l2O_om_apply_eq_of_isThetaFunO hom hμ.1 hμ.2.1 hg, sobO_zero, ENNReal.coe_one, one_mul]
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * B, fun l hl x hx g hg => ?_⟩
    obtain ⟨g1, h1⟩ := x
    have hne : l ≠ [] := by rintro rfl; simp at hl
    rw [← List.dropLast_append_getLast hne, wordAct_append, wordAct_cons, wordAct_nil]
    set a := l.getLast hne
    have e := dRho_om hom hθ g1 h1 a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) hg
    have e' : heisDer ψ θ a (om (g1, h1) g) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1
        (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) (om (g1, h1) g) := rfl
    rw [e', e]
    have hg' := GlobalTheory.OrientedHeis.theta_dRho hθ hom.std a.1 (compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) hg
    have hs : ENNReal.ofReal (∑ i, ∑ j, (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
        |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        ≤ B := by
      rw [← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hB _ hx))
      unfold dirSize
      exact Finset.single_le_sum (f := fun a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool => ∑ i, ∑ j,
        (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
         |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        (fun b _ => by positivity) (Finset.mem_univ a)
    calc _ ≤ (C : ℝ≥0∞) * sobO ψ θ μ 𝓕 k _ := hC _ (by simp [hl]) _ hx _ hg'
      _ ≤ C * (ENNReal.ofReal _ * sobO ψ θ μ 𝓕 (k + 1) g) := by
          gcongr
          exact sobO_dRho_le hom.std hθ hg a.1 _ k
      _ ≤ C * (B * sobO ψ θ μ 𝓕 (k + 1) g) := by gcongr
      _ = ((C * B : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (k + 1) g := by push_cast; ring

end GlobalTheory.ThetaDens.WeilCompact


open GlobalTheory.ThetaDens.WeilCompact GlobalTheory.Size in
theorem GlobalTheory.ThetaDens.om_compact_sobCont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ K : Set (GA D S × GA D T), IsCompact K → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S T), IsOpen (U' : Set (WO S T)) ∧ (∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x ∈ K, om x f ∈ GlobalTheory.Size.thetaLevel ψ S T U') ∧ ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x ∈ K, sobO ψ θ μ 𝓕 d (om x f) ≤ C * sobO ψ θ μ 𝓕 d' f := by
  intro D ψ S T χS χT om hom θ hθ μ 𝓕 hμ K hK U hU
  let U' : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ x ∈ K, Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U}
      add_mem' := fun {a b} ha hb x hx => by
        rw [Set.mem_setOf_eq] at ha hb
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (a + b) ∈ U
        rw [actO_add']; exact U.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
        rw [actO_zero']; exact U.zero_mem
      neg_mem' := fun {a} ha x hx => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (-a) ∈ U
        rw [actO_neg']; exact U.neg_mem (ha x hx) }
  have hU' : IsOpen (U' : Set (WO S T)) := by
    refine U'.isOpen_of_mem_nhds (g := 0) ?_
    refine hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T))
      (P := fun u x => Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U) fun x _ => ?_
    have hc : Continuous fun p : WO S T × (GA D S × GA D T) => Formalism.IndefR.Datum.actO S T p.2.1⁻¹ p.2.2⁻¹ p.1 := by
      unfold Formalism.IndefR.Datum.actO
      exact (((continuous_mt_eq T).comp continuous_snd.snd.inv).matrix_mul continuous_fst).matrix_mul
        ((continuous_mt_eq S).comp continuous_snd.fst.inv.inv)
    refine (hU.preimage hc).mem_nhds ?_
    show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
    rw [actO_zero']; exact U.zero_mem
  obtain ⟨B0, hB0⟩ := hK.bddAbove_image (continuous_dirSize hθ S T).continuousOn
  have hB : ∀ x ∈ K, dirSize θ S T x ≤ (B0.toNNReal : ℝ) := fun x hx =>
    (hB0 ⟨x, hx, rfl⟩).trans (Real.le_coe_toNNReal B0)
  refine ⟨U', hU', fun f hf x hx => ⟨hom.om_pres x f hf.1, fun u hu h0 => ?_⟩, fun d => ?_⟩
  · obtain ⟨g, h⟩ := x
    have hv : Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u ∈ U := hu (g, h) hx
    have hv0 : (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
      unfold Formalism.IndefR.Datum.actO
      rw [Matrix.map_mul, Matrix.map_mul, h0]; simp
    calc heisO ψ S T u (om (g, h) f)
        = heisO ψ S T (Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u)) (om (g, h) f) := by
          rw [actO_actO_inv]
      _ = om (g, h) (heisO ψ S T (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u) f) := (hom.om_heis g h _ f hf.1).symm
      _ = om (g, h) f := by rw [hf.2 _ hv hv0]
  · choose C hC using word_om_le hom hθ hμ _ hB
    refine ⟨d, ∑ k ∈ Finset.range (d + 1), ∑ _a : Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, C k,
      fun f hf x hx => ?_⟩
    show wordSum (heisDer ψ θ) (l2O μ 𝓕) d (om x f) ≤ _
    unfold wordSum
    rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    calc _ ≤ (C k : ℝ≥0∞) * sobO ψ θ μ 𝓕 k f := hC k _ (List.length_ofFn) x hx f hf.1
      _ ≤ C k * sobO ψ θ μ 𝓕 d f := by
          gcongr
          exact sobO_mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelSobolevBoundWeilCompactStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_level_sobolev_bound_weil_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ K : Set (GA D S × GA D T), IsCompact K → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S T), IsOpen (U' : Set (WO S T)) ∧ (∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x ∈ K, om x f ∈ GlobalTheory.Size.thetaLevel ψ S T U') ∧ ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x ∈ K, sobO ψ θ μ 𝓕 d (om x f) ≤ C * sobO ψ θ μ 𝓕 d' f := by
  first | exact @GlobalTheory.ThetaDens.om_compact_sobCont | exact GlobalTheory.ThetaDens.om_compact_sobCont | (intros; apply GlobalTheory.ThetaDens.om_compact_sobCont <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaVectorFixedUnramifiedStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaVectorFixedUnramifiedStabilizer
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP.VacFix

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ v ∉ Sf, ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v, omh (emb D.sp.cm.sig (dblSp A).gram v k, 1) (delta A B Φ₁ Φ₂) = delta A B Φ₁ Φ₂ := by
  intro D ψ A B χB omh hW LA LB Sf Φ₁ Φ₂ h1 h2 hU v hv k hk
  have hstd := hW.std
  obtain ⟨hsd, hvac⟩ := GlobalTheory.T.doubling_sphericalVacua_to_doubled_lattice_vacuum D ψ A B LA LB hstd hU.sdA
  have hth := GlobalTheory.T.isThetaFunction_doublingSeesaw_of_standard_char D ψ A B hstd Φ₁ Φ₂ h1 h2
  have hlv := hvac Sf Φ₁ Φ₂ hU.sph₁ hU.sph₂ v hv
  have u1 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.UnramAt (1 : (AE D)ˣ →* Circle) v := fun _ _ _ _ => rfl
  have u2 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.UnramAt χB v := by
    obtain ⟨χ, hc⟩ := GlobalTheory.T.exists_heckeCharacter_of_unitary_tensorIdeles D χB hW.hecT
    refine GlobalTheory.UnramOver.unramAt_of_unrAt D χB χ hc v _ ?_ ?_
    · refine ⟨singleV _ v 1, rfl, ?_, ?_⟩
      · classical
        exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1
      · intro v' hv'
        classical
        exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 hv'
    · intro P hP
      exact (GlobalTheory.LFun.unrAt_iff_of_chrEq hc P).1 (hU.unr P (by
        simp only [GlobalTheory.LFun.above, Set.mem_setOf_eq, hP]
        exact_mod_cast hv))
  have key : ∀ C, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.VacuumFixedOn D C → C v →
      omh (emb D.sp.cm.sig (dblSp A).gram v k, 1) (delta A B Φ₁ Φ₂) = delta A B Φ₁ Φ₂ := by
    intro C hC hCv
    have := hC ψ (dblSp A) B 1 χB omh (sumLat finSumFinEquiv LA LA) LB hW hsd hU.sdB v hCv u1 u2 _ hth hlv k hk 1
      (one_mem _)
    rwa [map_one] at this
  by_cases hs : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsSplitPlace D v
  · exact key _ (GlobalTheory.PlaceTensor.splitVacuumFixed D) hs
  · exact key _ (GlobalTheory.PlaceTensor.inertVacuumFixed D) hs

end GlobalTheory.Core.Rk.IP.VacFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaVectorFixedUnramifiedStabilizerStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledTheta_vector_fixed_unramified_stabilizer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ v ∉ Sf, ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v, omh (emb D.sp.cm.sig (dblSp A).gram v k, 1) (delta A B Φ₁ Φ₂) = delta A B Φ₁ Φ₂ := by
  first | exact @GlobalTheory.Core.Rk.IP.VacFix.main | exact GlobalTheory.Core.Rk.IP.VacFix.main | (intros; apply GlobalTheory.Core.Rk.IP.VacFix.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSplitHalfLatticeCoordinatesIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSplitHalfLatticeCoordinatesIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.RdBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mul_mem (x : k) : ∃ N : ℕ, 0 < N ∧ (N : k) * x ∈ 𝒪[k] := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  set Q := Fintype.card (IsLocalRing.ResidueField 𝒪[k])
  have hQ : (Q : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hQ
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have h2 : b ∣ ((Q ^ m : ℕ) : 𝒪[k]) := by
    rw [hu, Units.mul_left_dvd, Nat.cast_pow]
    exact pow_dvd_pow_of_dvd hQ m
  obtain ⟨d, hd⟩ := h2
  refine ⟨Q ^ m, pow_pos Fintype.card_pos m, ?_⟩
  have hb1 : (algebraMap 𝒪[k] k b) ≠ 0 := fun h => hb0 (Subtype.ext h)
  have h3 : ((Q ^ m : ℕ) : k) = algebraMap 𝒪[k] k b * algebraMap 𝒪[k] k d := by
    rw [← map_mul, ← hd, map_natCast]
  have h4 : ((Q ^ m : ℕ) : k) * (algebraMap 𝒪[k] k a / algebraMap 𝒪[k] k b) = ((d * a : 𝒪[k]) : k) := by
    rw [h3]
    change _ = algebraMap 𝒪[k] k (d * a)
    rw [map_mul]
    field_simp
  rw [h4]
  exact (d * a).2

theorem exists_nat_mul_mem_family {ι : Type} [Fintype ι] (f : ι → k) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * f i ∈ 𝒪[k] := by
  classical
  choose n hn hf using fun i => exists_nat_mul_mem (f i)
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (n i : k), mul_assoc]
  exact mul_mem (natCast_mem _ c) (hf i)

end GlobalTheory.FinPl.RdBound


open GlobalTheory.FinPl.RdBound in
theorem GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), IsHalf p.e u → ∀ i j, (N : k) * rd α β u i j ∈ 𝒪[k] := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨K₁, hK₁, h₁⟩ := exists_nat_mul_mem_family (fun x : n × Fin T.rank => β.b' x.1 x.2)
  obtain ⟨K₂, hK₂, h₂⟩ := exists_nat_mul_mem_family (fun x : Fin S.rank × n' => α.b x.1 x.2)
  refine ⟨K₁ * M * K₂, Nat.mul_pos (Nat.mul_pos hK₁ hM) hK₂, fun u hu hh i j => ?_⟩
  have hu' := GlobalTheory.PlaceModel.latO_le_top _ hu
  have hint : ∀ a b, (M : k) * p.pr (u a b) ∈ 𝒪[k] := fun a b => by
    rw [p.int_iff]
    have h1 : p.sec ((M : k) * p.pr (u a b)) = (M : AE D) * u a b := by
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, p.sec_pr, hh a b]
    rw [h1]
    refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
    rw [RingHom.map_mul, map_natCast]
    exact hden _ hu' a b
  change (_ : k) * (β.b' * Matrix.map u p.pr * α.b) i j ∈ 𝒪[k]
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine sum_mem fun a _ => ?_
  have e : ((K₁ * M * K₂ : ℕ) : k) * (β.b' i a * Matrix.map u p.pr a b * α.b b j) =
      ((K₁ : k) * β.b' i a) * ((M : k) * p.pr (u a b)) * ((K₂ : k) * α.b b j) := by
    rw [Matrix.map_apply]; push_cast; ring
  rw [e]
  exact mul_mem (mul_mem (h₁ (i, a)) (hint a b)) (h₂ (b, j))

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSplitHalfLatticeCoordinatesIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_mul_splitHalf_latticeCoordinates_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), IsHalf p.e u → ∀ i j, (N : k) * rd α β u i j ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem | exact GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem | (intros; apply GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsAtTauChart
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RegSch.ChartDer

open GlobalTheory.StdUnn

variable {D : D7}

theorem isAtTau_iff (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (x : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V) :
    IsAtTau θ V τ x h ↔ compAt θ τ (mt V h) = x ∧ (∀ τ', τ' ≠ τ → compAt θ τ' (mt V h) = 1) ∧
      (mt V h).map (finPart D) = 1 := by
  have : h ∈ GinfC V ↔ (mt V h).map (finPart D) = 1 := by
    rw [GinfC, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [IsAtTau, this]
  exact ⟨fun ⟨a, b, c⟩ => ⟨b, c, a⟩, fun ⟨b, c, a⟩ => ⟨a, b, c⟩⟩

end GlobalTheory.RegSch.ChartDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowColumnShapeOfWindowDataWidthGeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowColumnShapeOfWindowDataWidthGeOne
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem rowColumnShape_of_windowData_width_ge_one : ∀ (D : D7) (C0 : ℝ), 1 ≤ C0 → StandingNumericalData D C0 → DataNW D := by
  intro D C0 hC0 h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, h11, h12, h13, h14⟩
  intro u
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  have hC : 0 < C0 := lt_of_lt_of_le one_pos hC0
  have hpos : 0 < (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 := by positivity
  have : (0 : ℝ) < (D.duS u : ℝ) := lt_of_lt_of_le hpos (h10 u).1
  exact_mod_cast this

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowColumnShapeOfWindowDataWidthGeOneStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataNW_of_standingNumericalData : ∀ (D : D7) (C0 : ℝ), 1 ≤ C0 → StandingNumericalData D C0 → DataNW D := by
  first | exact @GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one | exact GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one | (intros; apply GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageWittIndexLtAndPlacesTwoSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageWittIndexLtAndPlacesTwoSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.WittTwo

theorem wittIndex_lt_and_two_split : ∀ (D : D7) (c : Com D) (j : ℕ) (s : PiLocalization₂ D), j ≤ D.R.m → s.Is c j → GlobalTheory.Cusp.wittIndex s.V < D.R.t ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D c j s hj hs
  refine ⟨?_, fun v h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hpar : ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (s.V.gram.map τ) (sigYD D.R j).1 (sigYD D.R j).2 := by
    intro τ
    have h := hs.sigOK τ
    rw [hs.sig τ] at h
    exact h
  obtain ⟨W, hW, e⟩ := (GlobalTheory.Cusp.isGreatest_wittIndex (s.V : HSpace D.host.E)).1
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := GlobalTheory.ParallelWitt.finrank_le (E := D.host.E) s.V τ (hpar τ) W (fun x hx y hy => by
    have := hW hy
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this x hx)
  have h3 := D.R.three_m_lt_t
  simp only [sigYD] at h1
  omega

end GlobalTheory.ChainOnto.WittTwo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageWittIndexLtAndPlacesTwoSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_wittIndex_lt_and_places_two_split : ∀ (D : D7) (c : Com D) (j : ℕ) (s : PiLocalization₂ D), j ≤ D.R.m → s.Is c j → GlobalTheory.Cusp.wittIndex s.V < D.R.t ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split | exact GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split | (intros; apply GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split <;> assumption)
end
end
