module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isAdIso_eq_afIso (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (hι : GlobalTheory.TwU.IsAdIso ι) (x : AfE F E) : ι x = afIso F E x := by
  have key : ∀ P : HeightOneSpectrum (𝓞 E), ι x P = afIso F E x P := by
    intro P
    have ev : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a + b) P = a P + b P := fun _ _ => rfl
    have evm : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a * b) P = a P * b P := fun _ _ => rfl
    have evn : ∀ n : ℕ, ((n : FiniteAdeleRing (𝓞 E) E)) P = (n : P.adicCompletion E) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Nat.cast_succ, ev, ih, Nat.cast_succ]; rfl
    rw [← sub_eq_zero]
    by_contra hne
    set d := ι x P - afIso F E x P with hd
    have hv : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := F) (E := E) x {P} hv
    have hNP := hN P (Finset.mem_singleton_self P)
    have h1 : ι (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) = afIso F E (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) := by
      show ι (y ⊗ₜ[F] 1) = afIso F E (y ⊗ₜ[F] 1)
      rw [hι.1, afIso_tmul_one]
    have hd2 : d = (N : P.adicCompletion E) * (ι r P - afIso F E r P) := by
      rw [hd, e, map_add (f := _), map_add (f := _), h1, map_mul, map_mul, map_natCast, map_natCast]
      rw [ev, ev, evm, evm, evn]
      ring
    have hr1 : Valued.v (ι r P) ≤ 1 := (hι.2 r).1 hr P
    have hr2 : Valued.v (afIso F E r P) ≤ 1 := (mem_rInt_iff F E r).1 hr P
    have hsub : Valued.v (ι r P - afIso F E r P) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le hr1 hr2)
    have hle : Valued.v d ≤ Valued.v (N : P.adicCompletion E) := by
      rw [hd2, map_mul]
      exact mul_le_of_le_one_right' hsub
    exact lt_irrefl _ (hle.trans_lt hNP)
  exact Subtype.ext (funext key)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEqStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleFieldIdentification_eq_baseChangeRingEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E), GlobalTheory.TwU.IsAdIso ι → ∀ x, ι x = afIso F E x := by
  first | exact @GlobalTheory.isAdIso_eq_afIso | exact GlobalTheory.isAdIso_eq_afIso | (intros; apply GlobalTheory.isAdIso_eq_afIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdentificationTypeRepresentativesClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdentificationTypeRepresentativesClasses
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.RepCls

theorem reps_classes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F rep → ∃ e : Φ ≃ principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b))) (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0), ∀ π, (principalLevelFrame.rowRepR R.θ (e π)).Iso (rep π) ∧ (∀ b, y.prtE F b (principalLevelFrame.rowRepR R.θ (e π)) = y.prtE F b (rep π)) ∧ (∀ i, y.prtW F i (principalLevelFrame.rowRepR R.θ (e π)) = y.prtW F i (rep π)) ∧ ∃ b, y.prtE F b (rep π) ≠ ⊥ ∧ y.prtE F b (rep π) ≤ (y.C F).EEc b := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y Φ rep hR
  let f : Φ → principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0) :=
    fun π => Quotient.mk _ ⟨rep π, hR.mem π⟩
  have hinj : Function.Injective f := by
    intro π π' h
    exact hR.inj π π' (Quotient.exact h)
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨π, hπ⟩ := hR.all (Formalism.L2.Col.finTypRep _ c) (Formalism.L2.Col.finTypRep_mem _ c)
    refine ⟨π, ?_⟩
    rw [← Quotient.out_eq c]
    exact Quotient.sound hπ
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun π => ?_⟩
  have hiso : (principalLevelFrame.rowRepR R.θ (Equiv.ofBijective f ⟨hinj, hsurj⟩ π)).Iso (rep π) :=
    Formalism.L2.Col.finTypRep_mk_iso ⟨rep π, hR.mem π⟩
  refine ⟨hiso, fun b => ?_, fun i => ?_, ?_⟩
  · unfold Hd.prtE principalLevelFrame.isotE
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ (principalLevelFrame.conjT_iso hiso)]
  · unfold Hd.prtW
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ hiso]
  · obtain ⟨b, hb⟩ := hR.mem π
    refine ⟨b, ?_, ?_⟩
    · intro h
      apply hb
      unfold Hd.prtE at h
      rw [eq_bot_iff] at h ⊢
      intro x hx
      have h0 := h (Submodule.mem_map_of_mem hx)
      rw [Submodule.mem_bot] at h0 ⊢
      exact (LinearEquiv.map_eq_zero_iff _).1 h0
    · exact Submodule.map_mono inf_le_left

end GlobalTheory.Mem.R3.Rw.RepCls
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdentificationTypeRepresentativesClassesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_identification_typeRepresentatives_classes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F rep → ∃ e : Φ ≃ principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b))) (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0), ∀ π, (principalLevelFrame.rowRepR R.θ (e π)).Iso (rep π) ∧ (∀ b, y.prtE F b (principalLevelFrame.rowRepR R.θ (e π)) = y.prtE F b (rep π)) ∧ (∀ i, y.prtW F i (principalLevelFrame.rowRepR R.θ (e π)) = y.prtW F i (rep π)) ∧ ∃ b, y.prtE F b (rep π) ≠ ⊥ ∧ y.prtE F b (rep π) ≤ (y.C F).EEc b := by
  first | exact @GlobalTheory.Mem.R3.Rw.RepCls.reps_classes | exact GlobalTheory.Mem.R3.Rw.RepCls.reps_classes | (intros; apply GlobalTheory.Mem.R3.Rw.RepCls.reps_classes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeRepresentativesPartsOtherLaterStages
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeRepresentativesPartsOtherLaterStages
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Tr

theorem rowPsi_eq_of_psi {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl

theorem reps_parts_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → (∀ (Φ : Type) (rep : Φ → _), Reps y F rep → @Reps b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by exact rep))) ∧ (∀ bb π, HEq (@Hd.prtE b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb ((by exact π))) (y.prtE F bb π)) ∧ ∀ i π, HEq (@Hd.prtW b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) ((by exact i)) ((by exact π))) (y.prtW F i π) := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs
  letI := alg b iK
  have hY0 : (rowPsi a y'.PY).ψ = y.PY.ψ := (by with_unfolding_all exact ((eq_of_heq hs.PY) :))
  have hY : rowPsi a y'.PY = y.PY := rowPsi_eq_of_psi _ _ hY0
  have hW0 : (fun i => (rowPsi a (y'.PW i)).ψ) = (fun i => (y.PW i).ψ) := (by with_unfolding_all exact ((eq_of_heq hs.PW) :))
  have hW : ∀ i, rowPsi a (y'.PW i) = y.PW i := fun i => rowPsi_eq_of_psi _ _ (congrFun hW0 i)
  have hocc : HEq (y'.occ (face b F)) (y.occ F) := by
    unfold Hd.occ principalLevelFrame.OccRows principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.occ F)) :))
  have e : y'.occ (face b F) = y.occ F := (by with_unfolding_all exact ((eq_of_heq hocc) :))
  refine ⟨?_, ?_, ?_⟩
  · intro Φ rep h
    exact ⟨h.fin, fun π => by rw [e]; exact h.mem π, fun π π' hi => h.inj π π' hi, fun ρ hρ => h.all ρ (by rw [e] at hρ; exact hρ)⟩
  · intro bb π
    unfold Hd.prtE principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtE F bb π)) :))
  · intro i π
    unfold Hd.prtW
    rw [isotL_eq a b]
    delta isotLB
    rw [hW i]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtW F i π)) :))

end GlobalTheory.Mem.R3.Tr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeRepresentativesPartsOtherLaterStagesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeRepresentativesParts_otherLaterStages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → (∀ (Φ : Type) (rep : Φ → _), Reps y F rep → @Reps b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by exact rep))) ∧ (∀ bb π, HEq (@Hd.prtE b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb ((by exact π))) (y.prtE F bb π)) ∧ ∀ i π, HEq (@Hd.prtW b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) ((by exact i)) ((by exact π))) (y.prtW F i π) := by
  first | exact @GlobalTheory.Mem.R3.Tr.reps_parts_tr | exact GlobalTheory.Mem.R3.Tr.reps_parts_tr | (intros; apply GlobalTheory.Mem.R3.Tr.reps_parts_tr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBasisNear
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocFrame

section Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
open GlobalTheory.LieMet (tanOf isTan_tv isTan_map tan_ext)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T U : Type} [CommRing S] [CommRing T] [CommRing U] {x : Sp S ⟶ X} {x' : Sp T ⟶ X} {x'' : Sp U ⟶ X}

def res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (v : TanM x t.G) : TanM x' t.G := tanOf (isTan_map ψ hx (isTan_tv v))

theorem res_res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (χ : T →+* U) (hx' : spMap χ ≫ x' = x'') {ω : S →+* U}
    (e : χ.comp ψ = ω) (hx'' : spMap ω ≫ x = x'') (v : TanM x t.G) :
    res χ hx' (res ψ hx v) = res ω hx'' v := by
  subst e
  refine tan_ext ?_
  show spMap (Formalism.L2.Pj.dualMap χ) ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ _ = spMap (Formalism.L2.Pj.dualMap (χ.comp ψ)) ≫ _
  rw [← Category.assoc, spMap_comp_spMap]
  congr 2
  exact RingHom.ext fun a => by ext <;> simp [Formalism.L2.Pj.dualMap]

theorem res_sum (ψ : S →+* T) (hx : spMap ψ ≫ x = x') {κ : Type} [Fintype κ] (a : κ → S) (n : κ → TanM x t.G) :
    res ψ hx (∑ k, a k • n k) = ∑ k, ψ (a k) • res ψ hx (n k) := by
  subst hx
  have dual_alg : (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) =
      (algebraMap T (DualNumber T)).comp ψ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have eps_dual (b : S) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul b) =
      spMap (epsMul (ψ b)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
    rw [spMap_comp_spMap, spMap_comp_spMap]
    congr 1
    refine RingHom.ext fun z => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, epsMul, mul_comm]
  let ρ : overAt (spMap ψ ≫ x) (DualNumber T) ⟶ overAt x (DualNumber S) := Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dual_alg])
  let f : TanM x t.G →+ TanM (spMap ψ ≫ x) t.G :=
    AddMonoidHom.mk' (res ψ rfl) fun a b => by
      apply tan_ext
      have h := congrArg (fun f => f.left) (MonObj.comp_mul ρ (tv a) (tv b))
      rw [tv_add]
      exact h
  refine (map_sum f _ _).trans (Finset.sum_congr rfl fun k _ => tan_ext ?_)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (tv (n k)).left) (eps_dual (a k))).trans
    (Category.assoc _ _ _))


end Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

end GlobalTheory.LieLocFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorFlagDensityGlueLowerUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorFlagDensityGlueLowerUnitriangular
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q : ℕ}

theorem blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    (b : Matrix (Fin q) (Fin q) ℂ) :
    (fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b =
      fromBlocks (aᴴ * S.toBlocks₁₁ * a) (aᴴ * S.toBlocks₁₂ * b) (bᴴ * S.toBlocks₂₁ * a) (bᴴ * S.toBlocks₂₂ * b) := by
  conv_lhs => rw [← fromBlocks_toBlocks S]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

theorem schur_blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    {b : Matrix (Fin q) (Fin q) ℂ} (hb : IsUnit b.det) :
    schur ((fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b) = aᴴ * schur S * a := by
  have hb' : IsUnit bᴴ.det := by rw [det_conjTranspose]; exact hb.star
  rw [blockDiag_conj, schur, schur]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  rw [mul_nonsing_inv_cancel_left _ _ hb, nonsing_inv_mul_cancel_left _ _ hb']

theorem reindex_conj_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (A : Matrix (Fin r) (Fin r) ℂ)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) :
    reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (fromBlocks (uni w.2.2) 0 0 (uni w.2.1))ᴴ * shear (reindex e e A) (toMat w.1) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
  have h1 : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w)) := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  have h2 : fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) =
      (fromBlocks 1 (toMat w.1) 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
    simp [fromBlocks_multiply]
  rw [h1, reindex_uni_glue he, h2, shear]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)), IsUnit (shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det → dens A (glue e w) = dens (shear (reindex e e A) (toMat w.1)).toBlocks₂₂ w.2.1 * ‖(shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det‖ ^ (-(2 * p : ℤ)) * dens (schur (shear (reindex e e A) (toMat w.1))) w.2.2 := by
  intro r p q e he A w hS
  have hR := reindex_conj_glue he A w
  set S := shear (reindex e e A) (toMat w.1) with hSdef
  set H := (uni (glue e w))ᴴ * A * uni (glue e w) with hH
  have h22 : (reindex e e H).toBlocks₂₂ = (uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1 := by
    rw [hR, blockDiag_conj, toBlocks_fromBlocks₂₂]
  have hd : (reindex e e H).toBlocks₂₂.det = S.toBlocks₂₂.det := by
    rw [h22, det_mul, det_mul, det_conjTranspose, det_uni]; simp
  have hs : schur (reindex e e H) = (uni w.2.2)ᴴ * schur S * uni w.2.2 := by
    rw [hR, schur_blockDiag_conj _ _ (by rw [det_uni]; exact isUnit_one)]
  obtain ⟨m1, m2⟩ := GlobalTheory.T.leadingMinor_blockDecomposition r p q e he H (hd ▸ hS)
  rw [hd, hs] at m2
  rw [h22] at m1
  unfold dens
  rw [← hH, ← Equiv.prod_comp e.symm, Fintype.prod_sum_type]
  have a1 : ∀ a : Fin q, lminor H (e.symm (Sum.inr a)).castSucc =
      lminor ((uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1) a.castSucc := fun a => m1 _ _ (by simp [he.2])
  have a2 : ∀ a : Fin p, lminor H (e.symm (Sum.inl a)).castSucc =
      S.toBlocks₂₂.det * lminor ((uni w.2.2)ᴴ * schur S * uni w.2.2) a.castSucc := fun a => m2 _ _ (by simp [he.1])
  simp only [a1, a2, norm_mul, mul_zpow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← zpow_natCast, ← _root_.zpow_mul, neg_mul]
  ring

end GlobalTheory.FlagFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorFlagDensityGlueLowerUnitriangularStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)), IsUnit (shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det → dens A (glue e w) = dens (shear (reindex e e A) (toMat w.1)).toBlocks₂₂ w.2.1 * ‖(shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det‖ ^ (-(2 * p : ℤ)) * dens (schur (shear (reindex e e A) (toMat w.1))) w.2.2 := by
  first | exact @GlobalTheory.FlagFibre.dens_glue | exact GlobalTheory.FlagFibre.dens_glue | (intros; apply GlobalTheory.FlagFibre.dens_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowIdentificationsRealRowSideOfChainComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowIdentificationsRealRowSideOfChainComparison
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SideTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {y : Hd R} {b : Bool}
  {rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] {S : RowSide D EE} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE} {ty : Fin n → D.what₂.FT}
  {jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)}

def ids (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowIds S (y.C F) b where
  jE := (LinearEquiv.ofInjective t.jE t.jE_inj).trans (LinearEquiv.ofEq _ _ t.jE_range)
  jM μ hμ j h1 h2 := (LinearEquiv.ofInjective (t.jM μ j) (t.jM_inj μ ((hU μ).1 hμ) j h1 h2)).trans
    (LinearEquiv.ofEq _ _ (t.jM_range μ ((hU μ).1 hμ) j h1 h2))
  jX μ hμ := (S.multTop μ).toLinearEquiv.trans ((LinearEquiv.ofInjective (t.jX μ) (t.jX_inj μ ((hU μ).1 hμ))).trans
    (LinearEquiv.ofEq _ _ (t.jX_range μ ((hU μ).1 hμ))))
  prt π := y.prtE F b (rep π)

theorem real (hU : ∀ μ, Used0 D μ ↔ y.Us μ)
    (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩) :
    RowSideReal S (y.C F) b (ids hU t) bs ty := by
  exact {
    parY j hj := by
      show Mult.parB (Ptw D) (min j D.R.m) = Mult.parB (Ptw D) j
      rw [min_eq_left (by have := y.hm; omega)]
    lvl μ _ := GlobalTheory.HilbertLevels.eec_le_cc R F y.tupT y.hm y.hTop b μ
    lvlP μ _ j _ h2 := GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := y.hm; omega)
    lvlX μ _ := GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ
    ee x x' := t.jE_ip x x'
    mult μ hμ j h1 h2 x x' := t.jM_ip μ ((hU μ).1 hμ) j h1 h2 x x'
    multX _ μ hμ x x' := by
      rw [← (S.multTop μ).inner_map_map x x']
      exact t.jX_ip μ ((hU μ).1 hμ) _ _
    io0 _ μ hμ _ x v := by
      have hmem : t.jM μ 1 v ∈ (y.C F).CC b μ 1 :=
        GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by have := D.R.two_le_m; omega) ((ids hU t).jM μ hμ 1 le_rfl (by have := D.R.two_le_m; omega) v).2
      have e := t.io0 μ ((hU μ).1 hμ) x v hmem
      refine e.trans ?_
      rfl
    io0X h := absurd h (by have := D.R.two_le_m; omega)
    io μ hμ _ j h1 h2 x v := by
      have hmem : t.jM μ (j + 1) v ∈ (y.C F).CC b μ (j + 1) :=
        GlobalTheory.HilbertLevels.ccp_le R F y.tupT y.hm y.hTop b μ (by omega) ((ids hU t).jM μ hμ (j + 1) (by omega) h2 v).2
      exact (t.io μ ((hU μ).1 hμ) j h1 h2 x v hmem).trans rfl
    ioTop h μ hμ _ x v := by
      have hmem : t.jX μ (S.multTop μ v) ∈ (y.C F).CCX b μ :=
        GlobalTheory.HilbertLevels.ccxp_le R F y.tupT y.hm y.hTop b μ ((ids hU t).jX μ hμ v).2
      exact (t.ioTop μ ((hU μ).1 hμ) x v _ (cast_heq _ _) hmem).trans rfl
    ft σ := by
      have h := t.ft (ty σ)
      have hs : bs σ ∈ Submodule.span ℂ (bs '' {σ' | ty σ' = ty σ}) := Submodule.subset_span ⟨σ, rfl, rfl⟩
      rw [h] at hs
      exact hs
    prt_disj π π' h := t.disj π π' h
  }

end GlobalTheory.Mem.R3.Rw.SideTie


open GlobalTheory.Mem.R3.Rw.SideTie in
theorem GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y _ _ hU b rep EE _ _ _ S n bs ty jA t
  exact ⟨ids hU t, real hU t, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowIdentificationsRealRowSideOfChainComparisonStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowIdentifications_realRowSide_of_chainComparison : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  first | exact @GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie | exact GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie | (intros; apply GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPower
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPower
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem det_blocks_lower {S J : Type} [CommRing S] [Fintype J] [DecidableEq J] (m : J → ℕ)
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) (hz : ∀ τ i j, i < j → g τ i j = 0) {n : ℕ}
    (e : Fin n ≃ Σ τ : J, Fin (m τ)) :
    ((Matrix.blockDiagonal' g).submatrix e e).det = ∏ x : (Σ τ : J, Fin (m τ)), g x.1 x.2 x.2 := by
  rw [Matrix.det_submatrix_equiv_self, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun τ _ => Matrix.det_of_lowerTriangular _ fun i j hij => hz τ i j hij

theorem isCombAt_blocks {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {J : Type} [Fintype J] [DecidableEq J] {m : J → ℕ}
    (u : ∀ τ, Fin (m τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ τ i, IsTanAt x (u τ i))
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) {n : ℕ} (e : Fin n ≃ Σ τ : J, Fin (m τ)) (i : Fin n)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (h : IsCombAt x (u (e i).1) (g (e i).1 (e i).2) w) :
    IsCombAt x (fun j => u (e j).1 (e j).2) ((Matrix.blockDiagonal' g).submatrix e e i) w := by
  obtain ⟨N, _, _, v, ρ, -, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (hu τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  rw [hcomb] at h ⊢
  rw [h]
  congr 1
  simp only [Matrix.submatrix_apply]
  rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => Matrix.blockDiagonal' g (e i) p • b p.1 p.2), Fintype.sum_sigma]
  generalize e i = p
  obtain ⟨a, k⟩ := p
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro σ _ hσ
    simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hσ.symm, zero_smul, Finset.sum_const_zero]
  · simp

theorem rule_frBor : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (t : Ix Dw → Kˣ) (y y' : FrPt Xo c K) (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x), FrBor t y y' → Tied e y.s y.u Φ → Tied e y'.s y'.u Φ' → κ K Φ'.key = kch t ^ 4 * κ K Φ.key := by
  classical
  intro κ hH hF E _ _ _ H Dw l Xo c g e K _ _ _ t y y' Φ Φ' hb hT hT'
  obtain ⟨M, hz, hd, hx, hc, hs⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 hb
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hc hs Φ Φ' hT hT'
  subst hx
  obtain ⟨h1, hg, hv⟩ := hT
  obtain ⟨h1', hg', hv'⟩ := hT'
  subst hg'
  have hid : x' = spMap (RingHom.id K) ≫ x' := by rw [GlobalTheory.Frames.SecCalc.spMap_id', Category.id_comp]
  have did : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    have hd : dualMap (RingHom.id K) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [hd]
    exact Spec.map_id _
  obtain ⟨th, hth⟩ := (GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.1 s
  have hne := ((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.2 th s hth).2.1
    (((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ.T.t Φ.m).2.2 Φ.th s h1).2.2 Φ.th_ne)
  have hss : GlobalTheory.Frames.SecBC (RingHom.id K) 1 x' x' s s :=
    ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo K K K _ _ x' x' x' hid hid).2.1 1 s s).2 fun i => by
      rw [GlobalTheory.Frames.SecCalc.scal_one', _root_.one_mul]
  have fibKey_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → GlobalTheory.Frames.SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
    intro E _ _ _ H Dw l Xo S S' _ _ hS φ x x' Φ Φ' s s' hx ht ht' hs
    obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ x x' (spMap φ) Φ.m Φ'.m hx).1
    obtain ⟨hg, -, w, hw⟩ := (pat_pullback E H S S' φ Φ.T).2 Φ'.T n hS
    obtain ⟨θ, hθ⟩ := GlobalTheory.ArcQBC.exists_pullSec n.φ Φ.th
    have hm : IsoMaps w Φ'.th θ := ((TieCalc.secTie_calc E H Dw l Xo S x Φ.T.t Φ.m Φ.th s ht).2 S' φ x' Φ'.T.t Φ'.m n s' w θ
      Φ'.th hx hn.symm hs hw hθ).1 ht'
    obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange S S' φ Φ.T.t.G Φ'.T.t.G n.φ n.cart Φ.T.t.semi.smooth Φ.T.g Φ.v Φ.basis
    have hb : ∀ (k : ℕ) (hk : k = Φ.T.g), IsLieBasis fun i : Fin k => u (i.cast hk) := by
      rintro _ rfl
      exact hu
    have hv : ∀ i : Fin Φ'.T.g, (u (i.cast hg)).left ≫ n.φ = spMap (dualMap φ) ≫ (Φ.v (i.cast hg)).left :=
      fun i => huv _
    have he : eSec Φ'.T.t.G ≫ n.φ = spMap φ ≫ eSec Φ.T.t.G := n.cm.e_comm.trans (congrArg (· ≫ eSec Φ.T.t.G) n.base)
    have hr : ∀ (e : Sp S' ⟶ Sp S) (_ : n.cm.e = e) (he : eSec Φ'.T.t.G ≫ n.φ = e ≫ eSec Φ.T.t.G),
        rigPullOf n.φ e he Φ.T.t.PP.L Φ.T.t.PP.rig = n.cm.rigPull Φ.T.t.PP.L Φ.T.t.PP.rig := by
      rintro _ rfl _
      rfl
    refine ⟨hg, fun i => u (i.cast hg), hb _ hg, ⟨n.φ, he, w, hg, dualMap φ, n.cart, hw.1, ?_, fun j i h => ?_,
      fun a => ?_, ?_, hv⟩, fun i => ?_⟩
    · exact (hr _ n.base he).symm ▸ hw.2
    · refine Eq.trans ?_ (hm j i)
      have le : (Φ.T.t.PP.L.pull n.φ).U j ≤ n.φ ⁻¹ᵁ Φ.T.t.PP.L.U (j PUnit.unit) := fun y hy => mem_pull.1 hy
      rw [hθ j le, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    · ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · ext <;> simp [dualMap]
    · rw [← hn, ← Category.assoc, hv, Category.assoc]
  obtain ⟨hg2, v, hvb, hpb, hvv⟩ := fibKey_keyPB E H Dw l Xo K K (RingHom.id K) x' x' Φ
    { Φ' with th := th, th_ne := hne } s s hid h1 hth hss
  have hvu : ∀ i : Fin Φ'.T.g, (v i).left ≫ Φ'.m.φ = u (e i).1 (e i).2 := fun i => by
    refine (hvv i).trans ?_
    rw [did, Category.id_comp]
    exact hv _
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have hsc := ((TieCalc.secTie_calc E H Dw l Xo K x' Φ'.T.t Φ'.m th s hth).1 _ x' s' Φ'.th rfl hs).1 h1'
  have hcomb : ∀ i, IsLieComb ((Matrix.blockDiagonal' M).submatrix e e i) v (Φ'.v i) := fun i => by
    have h2 := isCombAt_blocks u tan M e i _ (hc (e i).1 (e i).2)
    rw [← funext hvu] at h2
    obtain ⟨w, hw, hw'⟩ := (GlobalTheory.MetricChange.lift_comb Φ'.m.cart).2 _ _ v _ h2
    have : w = Φ'.v i := Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext (hw.trans (hv' i).symm) ((Over.w _).trans (Over.w _).symm))
    exact this ▸ hw'
  have e2 := hH K Φ'.T.pol Φ'.g_pos Φ'.T.t.PP.rig Φ'.T.t.PP.rigGen th hne v hvb Φ'.th Φ'.th_ne Φ'.v Φ'.basis
    (t none : K) _ hsc hcomb
  have e3 := (det_blocks_lower (fun τ => Dw.mult τ) M hz e).trans (Finset.prod_congr rfl fun x _ => hd x.1 x.2)
  have e4 : ((t none : K)) ^ 8 * (κ K Φ'.key : K) =
      (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (t (some x) : K)) ^ 4 * (κ K Φ.key : K) := by
    refine e2.trans ?_
    exact congrArg₂ (fun a b : K => a ^ 4 * b) e3 e1
  apply Units.ext
  have h0 : (t none : K) ≠ 0 := Units.ne_zero _
  rw [kch_eq]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_prod]
  field_simp
  linear_combination e4

end GlobalTheory.KeyFourth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPowerStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (t : Ix Dw → Kˣ) (y y' : FrPt Xo c K) (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x), FrBor t y y' → Tied e y.s y.u Φ → Tied e y'.s y'.u Φ' → κ K Φ'.key = kch t ^ 4 * κ K Φ.key := by
  first | exact @GlobalTheory.KeyFourth.rule_frBor | exact GlobalTheory.KeyFourth.rule_frBor | (intros; apply GlobalTheory.KeyFourth.rule_frBor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLift
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLift
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT


open Classical GlobalTheory.TopStep in
theorem sub_mem_stdAt_of_redV {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (m : GLint E n P) (x : Sp E n)
    (hx : (qOf P : E) • x ∈ stdAt E n P) (hred : ∀ v ∈ stdAt E n P, redV P (m.1 v) = redV P v) :
    m.1 x - x ∈ stdAt E n P := by
  have hq0 : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hk0 := glint_mem m hx
  refine mem_stdAt.2 fun j => ?_
  have hi1 := mem_stdAt.1 hk0 j
  have hi2 := mem_stdAt.1 hx j
  have hr : redP P ((m.1 ((qOf P : E) • x) - (qOf P : E) • x) j) = 0 := by
    rw [Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]
    exact congrFun (hred _ hx) j
  have := intAt_div_of_redP hq (intAt_sub hi1 hi2) hr
  convert this using 1
  rw [LinearEquiv.map_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp


set_option maxHeartbeats 1600000 in
open Classical GlobalTheory.TopStep in
theorem cosetIn_act_of_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), (I.stp u a i).gam b κ = 1 → LiftsInv I κ P g → ∀ z, z ∈ cosetIn ((I.stp u a i).act b κ p) P ↔ g z ∈ cosetIn p P := by
  intro B X I _ u a i b κ p P g hgam hL z
  have hX : B.fields.Ok := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hPr : (B.primes X).Ok := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨γ, h, c⟩ := κ
  have hγ : γ = 1 := by
    have e : ufGL B.fields.E (B.R.N i) γ = 1 := hgam
    have e2 : (toGLm B.fields.E (B.R.N i)) γ.1 = (toGLm B.fields.E (B.R.N i)) 1 := by
      rw [map_one]; exact e
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective e2)
  subst hγ
  set p' := (I.stp u a i).act b ((1 : UF B.fields.E (B.R.N i)), h, c) p with hp'
  have hys : p'.1.2 = p.1.2 := by
    show (fun v => ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) v) '' p.1.2 = p.1.2
    simp
  have hg : ∀ x, g x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := hL.1
  have key : ∀ y ∈ p.1.2, ((qOf P.1 : B.fields.E) ^ (if P.1 ∈ (B.primes X).vGs then 0 else (I.cst a).M))⁻¹ •
      (g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
    intro y hy
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · rw [if_pos hP, pow_zero, inv_one, one_smul]
      by_cases hj : i + 1 = B.R.m
      swap
      · have h0 : p.1.2 = ∅ := by
          have := p.2
          rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj] at this
          exact this
        rw [h0] at hy
        exact absurd hy (Set.notMem_empty y)
      obtain ⟨y0, hy0, hY⟩ := PtAt.mem_ybSet p hj
      have hy' : y - y0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) p.1.1.deco.1.N
          (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ)) := by
        rw [hY] at hy
        exact hy
      have hA : (qOf P.1 : B.fields.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy0 P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy' P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hx : (qOf P.1 : B.fields.E) • y ∈ p.1.1.deco.1.at P.1 := by
        have e : (qOf P.1 : B.fields.E) • y = (qOf P.1 : B.fields.E) • y0 + (qOf P.1 : B.fields.E) • (y - y0) := by
          rw [← smul_add, add_sub_cancel]
        rw [e]
        exact add_mem hA (smul_mem_locP (intAt_nat _) hB)
      let w : (B.primes X).vGs := ⟨P.1, hP⟩
      have hd : p'.1.1.deco.1 = p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1 := rfl
      have hf : IsLiftFr p.1.1.deco.1 w (p.1.1.deco.1.liftFr w) := liftFr_spec p.1.1.deco.2 w
      have hf' : IsLiftFr (p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1) w (p'.1.1.deco.1.liftFr w) := by
        rw [← hd]
        exact liftFr_spec p'.1.1.deco.2 w
      have e1 : frsF I.sel (I.tup a) p.1.1 P = p.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      have e2 : frsF I.sel (I.tup a) p'.1.1 P = p'.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      rw [e1, e2]
      have e3 : (p'.1.1.deco.1.liftFr w).symm y = (passFr (w := w) _ h.1 hf hf').1 ((p.1.1.deco.1.liftFr w).symm y) := by
        show _ = (p'.1.1.deco.1.liftFr w).symm (((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) ((p.1.1.deco.1.liftFr w) ((p.1.1.deco.1.liftFr w).symm y)))
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [e3]
      have hv0 : (qOf P.1 : B.fields.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        rw [← LinearEquiv.map_smul, ← hf.1, LinearEquiv.apply_symm_apply]
        exact hx
      have hκ : GlobalTheory.TopStep.redGL (B.R.N i) P.1 (passFr (w := w) _ h.1 hf hf') = h.1 w := redGL_passFr (w := w) _ h.1 hf hf'
      have hq := (degOneUnram_of_mem_vGs hX hPr hP).2
      have hred : ∀ v ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g ((passFr (w := w) _ h.1 hf hf').1 v)) = redV P.1 v := by
        intro v hv
        rw [hL.2.1 hP _ (glint_mem _ hv), redV_redGL _ hv, hκ, Matrix.mulVec_mulVec]
        show ((h.1 w)⁻¹.1 * (h.1 w).1).mulVec _ = _
        rw [Units.inv_mul, Matrix.one_mulVec]
      have hm := sub_mem_stdAt_of_redV P.1 hq (⟨g, hL.1⟩ * passFr (w := w) _ h.1 hf hf') _ hv0 hred
      exact hm
    · rw [if_neg hP]
      have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      have hF' : frsF I.sel (I.tup a) p'.1.1 P = frsF I.sel (I.tup a) p.1.1 P * g := by
        unfold frsF
        rw [dite_eq_right hP, dite_eq_right hP, hL.2.2 hQ]
        exact LinearEquiv.ext fun x => rfl
      have e : g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) = (frsF I.sel (I.tup a) p.1.1 P).symm y := by
        rw [eq_comm, LinearEquiv.symm_apply_eq]
        rw [hF']
        exact ((frsF I.sel (I.tup a) p.1.1 P * g).apply_symm_apply y).symm
      rw [e, sub_self, smul_zero]
      exact zero_mem _
  simp only [cosetIn, Set.mem_ofPred_eq]
  rw [hys]
  constructor
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := add_mem ((hg _).2 hz) (key y hy)
    rwa [map_smul, map_sub, ← smul_add, sub_add_sub_cancel] at this
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := sub_mem hz (key y hy)
    rw [← smul_sub, sub_sub_sub_cancel_right, ← map_sub, ← map_smul] at this
    exact (hg _).1 this

end GlobalTheory.Mem.Col2.AdT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLiftStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetInFrames_preimage_under_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), (I.stp u a i).gam b κ = 1 → LiftsInv I κ P g → ∀ z, z ∈ cosetIn ((I.stp u a i).act b κ p) P ↔ g z ∈ cosetIn p P := by
  first | exact @GlobalTheory.Mem.Col2.AdT.cosetIn_act_of_liftsInv | exact GlobalTheory.Mem.Col2.AdT.cosetIn_act_of_liftsInv | (intros; apply GlobalTheory.Mem.Col2.AdT.cosetIn_act_of_liftsInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueRuleOfRegular
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FlagTan

namespace GlobalTheory.ShFam

namespace Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

section Cpt

variable (C : FlagCpt Z e)

def Fk : Type := C.Y.Fn

instance : Field (Fk C) := inferInstanceAs (Field C.Y.Fn)

instance : Algebra c.F (Fk C) := RingHom.toAlgebra (constF e C.Y : c.F →+* C.Y.Fn)

def St (y : C.Y.X) : Type := C.Y.X.presheaf.stalk y

instance (y : C.Y.X) : CommRing (St C y) := inferInstanceAs (CommRing (C.Y.X.presheaf.stalk y))

def pt (y : C.Y.X) : Sp (St C y) ⟶ C.Y.X := stalkPt C.Y y

instance (y : C.Y.X) : Mono (pt C y) := inferInstanceAs (Mono (C.Y.X.fromSpecStalk y))

instance (y : C.Y.X) : Algebra c.F (St C y) := (Spec.preimage (pt C y ≫ C.π ≫ genStr Z)).hom.toAlgebra

theorem pt_str (y : C.Y.X) : pt C y ≫ C.π ≫ genStr Z = spMap (algebraMap c.F (St C y)) := (Spec.map_preimage _).symm

def gpt : Sp (Fk C) ⟶ C.Y.X := genericPt C.Y

def fr0 : FrPt Xo c (Fk C) := C.y0

theorem frame_point_over : GlobalTheory.AllWt.ptF (fr0 C) ≫ Z.jQ = gpt C ≫ C.π := C.y0_x

theorem str_of_over {T : Type} [CommRing T] [Algebra c.F T] {z : FrPt Xo c T} {x : Sp T ⟶ gen Z}
    (h : GlobalTheory.AllWt.ptF z ≫ Z.jQ = x) : x ≫ genStr Z = spMap (algebraMap c.F T) := by
  rw [← h, Category.assoc, Z.jQ_over, ptF_snd]


variable {C} in
def algOf {T : Type} [CommRing T] [Algebra c.F T] {y : C.Y.X} (ψ : St C y →+* T) {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (hp : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) : St C y →ₐ[c.F] T :=
  { ψ with commutes' := fun a => DFunLike.congr_fun (sp_inj (f := ψ.comp (algebraMap c.F (St C y))) (by
      rw [← sp_comp, ← pt_str, ← Category.assoc, h, hp])) a }

def toFkR (y : C.Y.X) : St C y →+* Fk C := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField

theorem toFkR_pt (y : C.Y.X) : spMap (toFkR C y) ≫ pt C y = gpt C :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

def toFk (y : C.Y.X) : St C y →ₐ[c.F] Fk C :=
  algOf (toFkR C y) (toFkR_pt C y) (by rw [← Category.assoc]; exact str_of_over (frame_point_over C))

theorem toFk_pt (y : C.Y.X) : spMap (toFk C y).toRingHom ≫ pt C y = gpt C := toFkR_pt C y

theorem toFk_injective (y : C.Y.X) : Function.Injective (toFk C y) :=
  IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField

variable {C}

theorem specializes_of {T : Type} [CommRing T] {y : C.Y.X} {ψ : St C y →+* T} {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (s : Sp T) : p s ⤳ y := by
  have : p s ∈ Set.range (C.Y.X.fromSpecStalk y) := ⟨spMap ψ s, by rw [← h]; rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

theorem hom_eq {T : Type} [CommRing T] {y : C.Y.X} {ψ ψ' : St C y →+* T} (h : spMap ψ ≫ pt C y = spMap ψ' ≫ pt C y) :
    ψ = ψ' := sp_inj ((cancel_mono _).1 h)

theorem exists_spec {y y' : C.Y.X} (h : y' ⤳ y) : ∃ sp : St C y →ₐ[c.F] St C y',
    spMap sp.toRingHom ≫ pt C y = pt C y' ∧ ∀ a, toFk C y' (sp a) = toFk C y a := by
  have k : spMap (R := St C y) (R' := St C y') (C.Y.X.presheaf.stalkSpecializes h).hom ≫ pt C y = pt C y' :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  refine ⟨algOf _ k (pt_str C y'), k, fun a => ?_⟩
  refine DFunLike.congr_fun (hom_eq (ψ := (toFk C y').toRingHom.comp (algOf _ k (pt_str C y')).toRingHom)
    (ψ' := (toFk C y).toRingHom) ?_) a
  rw [← sp_comp, Category.assoc, toFk_pt]
  exact (congrArg (_ ≫ ·) k).trans (toFk_pt C y')


variable (C) in
def rationalEigenFrame : EigFrame Z (algebraMap c.F (Fk C)) (gpt C ≫ C.π ≫ genι Z) := C.f0


variable (C) in
structure Chart (y : C.Y.X) (P : FrPt Xo c (St C y)) (t : Ix Dw → (Fk C)ˣ) : Prop where
  ov : GlobalTheory.AllWt.ptF P ≫ Z.jQ = pt C y ≫ C.π
  bm : BM (toFk C y) t P (fr0 C)

end Cpt

section Wit

variable {C : FlagCpt Z e} {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']


variable (C) in
structure Wit (p : Sp T ⟶ C.Y.X) (z : FrPt Xo c T) : Type where
  y : C.Y.X
  ψ : St C y →ₐ[c.F] T
  P : FrPt Xo c (St C y)
  t : Ix Dw → (Fk C)ˣ
  t' : Ix Dw → Tˣ
  chart : Chart C y P t
  hp : spMap ψ.toRingHom ≫ pt C y = p
  bm : BM ψ t' P z

variable {p : Sp T ⟶ C.Y.X} {z : FrPt Xo c T}

theorem Wit.ov (w : Wit C p z) : GlobalTheory.AllWt.ptF z ≫ Z.jQ = p ≫ C.π := by
  rw [ptF_map w.bm.x_eq, Category.assoc, w.chart.ov, ← Category.assoc, w.hp]

theorem carries_iff {k : Type} [Field k] {p : Sp k ⟶ C.Y.X} {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} :
    C.Carries p g ↔ ∃ (y : C.Y.X) (ψ : St C y →+* k) (φ₁ : c.F →+* St C y)
    (f : EigFrame Z φ₁ (pt C y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fk C)ˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), p = spMap ψ ≫ pt C y ∧
      f.Tri (toFk C y).toRingHom (rationalEigenFrame C) t ∧ f.Tri ψ g t' := Iff.rfl

theorem dual_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

end Wit

section Global

variable {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (ex : Ix Dw → ℤ)
  (s : ∀ k, Fk (Φ.C k)) {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']

variable {Φ ex s}

variable (hex : ex none = 0)
  (hs : ∀ k (y : (Φ.C k).Y.X), (Φ.C k).π y ∉ genBd Z → ((Φ.C k).LEx ex).RegularAt y (s k))

include hex hs


end Global

end Descent

end GlobalTheory.ShFam
end
end
