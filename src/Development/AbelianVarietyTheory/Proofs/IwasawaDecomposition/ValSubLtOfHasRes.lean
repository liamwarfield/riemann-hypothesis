module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubLtOfHasRes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PtStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_of_sub {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (hab : Valued.v (a - b) < 1) : HasRes P b c := by
  obtain ⟨r, hr, hv⟩ := h
  refine ⟨r, hr, ?_⟩
  have e : b - algebraMap E _ (algebraMap (𝓞 E) E r) = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (a - b) := by ring
  rw [e]
  exact Valuation.map_sub_lt _ hv hab

theorem val_sub_lt_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (h' : HasRes P b c) : Valued.v (a - b) < 1 := by
  obtain ⟨r, hr, hv⟩ := h
  obtain ⟨r', hr', hv'⟩ := h'
  have hmem : r - r' ∈ P.asIdeal := Ideal.Quotient.eq.1 (hr.trans hr'.symm)
  have e : a - b = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (b - algebraMap E _ (algebraMap (𝓞 E) E r')) +
      algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r - r')) := by
    simp only [map_sub]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sub_lt _ hv hv') ?_
  rw [valued_algebraMap]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hmem

theorem val_sub_lt_of_hatL {n : ℕ} (a b : Matrix (Fin n) (Fin n) (AfE F E)) (P : HeightOneSpectrum (𝓞 E)) (i : Fin n)
    {N : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ y ∈ N, Valued.v (adAt F P ((a *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i -
      (b *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i)) < 1)
    {z : Fin n → AfE F E} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) N) :
    Valued.v (adAt F P ((a *ᵥ z) i - (b *ᵥ z) i)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact h v hv
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (a *ᵥ (x + y)) i - (b *ᵥ (x + y)) i = ((a *ᵥ x) i - (b *ᵥ x) i) + ((a *ᵥ y) i - (b *ᵥ y) i) := by
      simp only [Matrix.mulVec_add, Pi.add_apply]
      ring
    rw [e, map_add (adAt F P)]
    exact Valuation.map_add_lt _ hx hy
  | smul c x _ hx =>
    have e0 : c • x = (c : AfE F E) • x := rfl
    have e : (a *ᵥ (c • x)) i - (b *ᵥ (c • x)) i = (c : AfE F E) * ((a *ᵥ x) i - (b *ᵥ x) i) := by
      rw [e0, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    rw [e, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 c.2 P)) hx

variable [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem pullV_mul_stab (g g' h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x =
      ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  unfold GlobalTheory.Mem.Col2.pullV
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]

theorem pullV_eq_of_mul (g h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV h x = ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
                 ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem val_sub_pullV_lt {g g' h : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q}
    (hg : IsPtOf hc g p) (hh : IsPtOf hc h q) {P : HeightOneSpectrum (𝓞 E)} (i : Fin n)
    (hP : ∀ y ∈ p.deco.1.N, Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV g y i - GlobalTheory.Mem.Col2.pullV g' y i)) < 1)
    {x : Sp E n} (hx : x ∈ q.deco.1.N) :
    Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV h x i - GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x i)) < 1 := by
  have hu : GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) :=
    (hh.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hz : (g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N := by
    refine (hg.lat _).2 ?_
    rwa [← pullV_eq_of_mul]
  have := val_sub_lt_of_hatL _ _ P i (fun y hy => hP y hy) hz
  rwa [← pullV_eq_of_mul, ← pullV_mul_stab] at this

theorem isPtOf_mul_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), ∀ (g g' h : GL (Fin n) (AfE F E)) (p q : DecoF E n ST SG Q), IsPtOf hc g p → IsPtOf hc g' p → IsPtOf hc h q → IsPtOf hc (h * (g⁻¹ * g')) q := by
  intro F E _ _ _ _ _ _ hc n ST SG Q g g' h p q hg hg' hh
  refine ⟨mul_mem hh.uni (mul_mem (inv_mem hg.uni) hg'.uni), fun x => ?_, fun P x hx i hi => ?_, fun w x hx i => ?_,
    fun P i j => ?_⟩
  · have e : (((h * (g⁻¹ * g'))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
        ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (((h⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e, hh.lat x, ← hg'.lat, hg.lat, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · refine hasRes_of_sub (hh.f P x hx i hi) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.f P y hy i hi) (hg'.f P y hy i hi)
  · refine hasRes_of_sub (hh.be w x hx i) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.be w y hy i) (hg'.be w y hy i)
  · have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) =
        (g' : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) := by
      ext a b
      simp only [Matrix.map_apply]
      rw [hg.fr, hg'.fr]
    have hs : (((g⁻¹ * g' : GL (Fin n) (AfE F E))) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) = 1 := by
      rw [Units.val_mul, Matrix.map_mul, ← hgg, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have e : adAt F P.1 (((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        ((((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F P.1)) i j := rfl
    rw [e, Units.val_mul, Matrix.map_mul, hs, mul_one, Matrix.map_apply]
    exact hh.fr P i j

end GlobalTheory.Mem.Col2.PtStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClasses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open scoped TensorProduct

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reL_refl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  simp only [reL, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_refl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  simp [reGL]

theorem fvTie_of_coords (hc : CMData F E) (S : HSpace E) {cls : Type}
    (y : cls → Formalism.L2.Herm.UAf hc S) (lat : cls → Submodule (𝓞 E) S.V)
    (w : HeightOneSpectrum (𝓞 F)) (k : Type) [AddCommGroup k]
    (fz : ∀ c, Formalism.HermitianLatticesTheory.dual S.hT (lat c) → k)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) {b : ℕ} (h : S.rank = b)
    (J : Matrix (Fin b) (Fin b) E) (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    (Lb' : Submodule (𝓞 E) (Fin b → E)) (hL : Lb' = reL h Lb)
    (y' : cls → GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ c, y' c = reGL h _ (y c).1)
    (fT : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb')) →+ k)
    (hfv : ∀ c (z : Formalism.HermitianLatticesTheory.dual S.hT (lat c))
      (hz : ((bc (prV (E := E) w) (y' c))⁻¹).1 *ᵥ
          (fun a => inclE (F := F) (w.adicCompletion F) (reV h E (Formalism.L2.Herm.crd S z.1) a)) ∈
        latS (F := F) (w.adicCompletion F) (intV E w)
          (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb'))),
      fz c z = fT ⟨_, hz⟩) :
    Nonempty (Formalism.L2.Herm.FvTie hc S Lb y lat w k fz) := by
  subst h
  obtain rfl : J = S.gram := by rw [hJ]; ext i j; simp
  obtain rfl : Lb' = Lb := hL.trans (reL_refl Lb)
  obtain rfl : y' = fun c => (y c).1 := funext fun c => (hy c).trans (reGL_refl _ _)
  refine ⟨⟨fT, fun c z t ht => ?_⟩⟩
  have ht' : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) = t.1 := by
    have e : (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) =
        fun a => inclE (F := F) (w.adicCompletion F) (Formalism.L2.Herm.crd S z.1 a) := rfl
    rw [e, ← ht, Matrix.mulVec_mulVec]
    simp
  have hz : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) S.gram Lb')) := by
    rw [ht']; exact t.2
  rw [hfv c z hz]
  exact congrArg fT (Subtype.ext ht')

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (G : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (G.reindex (finCongr h) (finCongr h)) (reV h E x) (reV h E y) = hform σ G x y := by
  subst h
  have e : (G.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) = G := by ext i j; simp
  rw [e]; rfl

end Generic

theorem crdN_mem_Ld {D : D7} (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ Ld D u i hi c := by
  refine Submodule.subset_span ?_
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  have h1 : (D.sp.X i).hT x0 z.1 ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := z.2
    simp only [Formalism.L2.Herm.Ld, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf] at this
    exact this x0 hx0
  rw [Formalism.L2.Herm.hT_crd D.sp.cm] at h1
  have h2 := hform_reindex (rankN D i hi) (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd _ x0) (Formalism.L2.Herm.crd _ z.1)
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
  exact ⟨r, hr.trans h2.symm⟩


set_option maxHeartbeats 4000000 in
theorem fvTie_top {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A) (u : D.what₂.Word)
    (h1 : 1 ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u D.R.m) :
    Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl β).Lb (H.cls u D.R.m h1 le_rfl β).y
      (fun c => D.clsLat u D.R.m c.1) (H.vT u v).1 ((D.mem u).A.Fv v)
      (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
  obtain rfl : β = chM H u := @Subsingleton.elim _ (@Unique.instSubsingleton _ (H.Ch_m u).some) _ _
  have key : ∀ w, w = ((F u).atT.eV v).1 →
      Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl (chM H u)).Lb
        (H.cls u D.R.m h1 le_rfl (chM H u)).y (fun c => D.clsLat u D.R.m c.1) w ((D.mem u).A.Fv v)
        (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
    intro w hw
    subst hw
    have hc := hH.carM u
    refine fvTie_of_coords D.sp.cm (D.sp.X D.R.m) _ _ _ _ _ _ (rankN D D.R.m le_rfl) (gramN D D.R.m le_rfl) rfl
      ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.Lb hc.Lb_eq
      (fun c => (((F u).cls D.R.m le_rfl (Or.inr rfl)).y c.1).1) (fun c => hc.y_eq c.1)
      (((F u).fMe D.R.m le_rfl (Or.inr rfl) v).toAddMonoidHom.comp
        (((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.fT _ ((F u).atT.eV v).2).toAddMonoidHom) ?_
    intro c z hz
    have hz' := crdN_mem_Ld u D.R.m le_rfl c.1 z
    have e1 := (F u).fv D.R.m le_rfl (Or.inr rfl) v c.1 ⟨_, hz'⟩ hz
    have e2 := hT.pr u D.R.m le_rfl v c.1 z ⟨_, hz'⟩ rfl
    exact (congrArg (fun p => (D.fm u).fv D.R.m v c.1 p) e2.symm).trans e1
  exact key _ (by rw [hH.eV u])


set_option maxHeartbeats 4000000 in
theorem fvTie_chart_top : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (h1 : 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u (I.rec7 l Z).R.m), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (H.lev u (I.rec7 l Z).R.m h1 le_rfl β).Lb (H.cls u (I.rec7 l Z).R.m h1 le_rfl β).y (fun c => (I.rec7 l Z).clsLat u (I.rec7 l Z).R.m c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv (I.rec7 l Z).R.m v c.1 ((A u).pr (I.rec7 l Z).R.m v c.1 z))) := by
  intro B X I _ _ l Z H F A _ hH hT u h1 v β
  exact fvTie_top H F A hH hT u h1 v β

end GlobalTheory.Mem.Col2.TC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClassesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFunctional_chart_lastStep_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (h1 : 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u (I.rec7 l Z).R.m), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (H.lev u (I.rec7 l Z).R.m h1 le_rfl β).Lb (H.cls u (I.rec7 l Z).R.m h1 le_rfl β).y (fun c => (I.rec7 l Z).clsLat u (I.rec7 l Z).R.m c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv (I.rec7 l Z).R.m v c.1 ((A u).pr (I.rec7 l Z).R.m v c.1 z))) := by
  first | exact @GlobalTheory.Mem.Col2.TC.fvTie_chart_top | exact GlobalTheory.Mem.Col2.TC.fvTie_chart_top | (intros; apply GlobalTheory.Mem.Col2.TC.fvTie_chart_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LpUnrNegOneSpec
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

section

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

abbrev WDAt (N : NData R H what₂) (w : PlE H) : Type :=
  WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)

abbrev UnrWDFam (N : NData R H what₂) (a : ℕ) : Type :=
  {p : (∀ w, WDAt N w) × ((H.E →+* ℂ) → Multiset ℂ) //
    (∀ w, (p.1 w).unr ∧ (p.1 w).lpDim = a) ∧ ∀ τ, Multiset.card (p.2 τ) = a}

theorem lpUnr_negOne_spec (N : NData R H what₂) (w : PlE H) :
    (WD.lpUnr (h := N.plOm.2 w) {-1}).unr ∧
      (WD.lpUnr (h := N.plOm.2 w) {-1}).frobEig = {-1} ∧
      (WD.lpUnr (h := N.plOm.2 w) {-1}).lpDim = 1 := by
  obtain ⟨hu, he, hd⟩ := WD.lpUnr_spec (h := N.plOm.2 w) ({-1} : Multiset ℂ) (by simp)
  exact ⟨hu, he, hd.trans (Multiset.card_singleton _)⟩

def negOneWDFam (N : NData R H what₂) : UnrWDFam N 1 :=
  ⟨(fun w => WD.lpUnr (h := N.plOm.2 w) {-1}, fun _ => {0}),
    fun w => ⟨(lpUnr_negOne_spec N w).1, (lpUnr_negOne_spec N w).2.2⟩, fun _ => rfl⟩

theorem UnrWDFam.exists_frobEig {N : NData R H what₂} (χ : UnrWDFam N 1) (w : PlE H) :
    ∃ c, (χ.1.1 w).frobEig = {c} := by
  have hu : (χ.1.1 w).unr := (χ.2.1 w).1
  have hd : (χ.1.1 w).lpDim = 1 := (χ.2.1 w).2
  have hc : Multiset.card (χ.1.1 w).frobEig = 1 := ((WD.unramified_laws (N.plOm.2 w)).2.2.2.2.2.2.2.2.2.2.2.2.1 _ hu).trans hd
  exact Multiset.card_eq_one.mp hc


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def nAutWD (N : NData R H what₂) (hE : IsEmpty N.Loc) (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) : NAut N where
  LP := WDAt N
  lpDim := WD.lpDim
  lpZero := fun w => WD.lpZero (h := N.plOm.2 w)
  lpSum := WD.lpSum
  lpTw := WD.lpTw
  lpChar := WD.lpChar
  lpUnr := fun w => WD.lpUnr (h := N.plOm.2 w)
  mono0 := WD.mono0
  unr := WD.unr
  frobEig := WD.frobEig
  tempered := WD.tempered
  inePol := WD.inePol
  items₂ := fun k w a => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab (τ k) (γ k w) a
  lpDim_zero := fun w => WD.lpDim_zero _
  lpDim_sum := WD.lpDim_sum
  lpDim_tw := WD.lpDim_tw
  lpUnr_spec := fun _ => WD.lpUnr_spec
  unr_sum := WD.unr_sum
  monomial_sum_iff := WD.monomial_sum_iff
  frobEig_sum := fun a b _ _ => WD.frobEig_lpSum a b
  unr_tw := WD.unr_tw
  monomial_twist_iff := WD.monomial_twist_iff
  frobEig_tw := WD.frobEig_tw
  frobEig_char := fun a χ c ha hχ _ => WD.frobEig_char a χ c ha hχ
  lpDim_char := WD.lpDim_char
  unr_char := fun a χ _ => WD.unr_lpChar a χ
  monomial_char_iff := WD.monomial_char_iff
  lpZero_unr := fun _ => WD.lpZero_unr
  frobEig_zero := fun _ => WD.frobEig_zero
  lpSum_zero := WD.lpSum_zero
  lpSum_comm := WD.lpSum_comm
  lpSum_assoc := WD.lpSum_assoc
  lpTw_zero := WD.lpTw_zero
  lpTw_add := WD.lpTw_add
  lpTw_sum := WD.lpTw_sum
  unr_eq_lpUnr := WD.unr_eq_lpUnr
  unr_mono0 := WD.unr_mono0
  frobEig_ne_zero := WD.frobEig_ne_zero
  frobEig_card := fun a _ => WD.card_eig a _
  tempered_unr := WD.tempered_unr
  inePol_sum := WD.inePol_sum
  inePol_tw := WD.inePol_tw
  unr_iff_ine := WD.unr_iff_ine
  inertiaCharpoly_zero := fun k w => by
    let : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    have hzero := WD.lpDim_zero (N.plOm.2 w)
    exact WD.lab_of_lpDim_eq_zero (τ k) (γ k w) hzero
  inertiaCharpoly_add := fun k _ a b => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab_lpSum _ _ a b
  CG := UnrWDFam N
  csd := fun π => ∀ w w', IsConjPl H w w' → (π.1.1 w').frobEig = (π.1.1 w).frobEig.map (·⁻¹)
  ralg := fun {a} π => ∀ τ, (π.1.2 τ).Nodup ∧ ∀ z ∈ π.1.2 τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  locG := fun π w => π.1.1 w
  locG_dim := fun π w => (π.2.1 w).2
  locG_unr_ae := fun π => Filter.Eventually.of_forall fun w => (π.2.1 w).1
  tw := fun π χ => ⟨(fun w => (π.1.1 w).lpChar (χ.1.1 w), fun τ => (π.1.2 τ).map (· + (χ.1.2 τ).sum)),
    fun w => ⟨WD.unr_lpChar _ _ (π.2.1 w).1 (χ.2.1 w).1, (WD.lpDim_char _ _ (χ.2.1 w).2).trans (π.2.1 w).2⟩,
    fun τ => (Multiset.card_map _ _).trans (π.2.2 τ)⟩
  locG_tw := fun _ _ _ => rfl
  infG := fun π τ => π.1.2 τ
  infG_card := fun π τ => π.2.2 τ
  ralg_def := fun _ => Iff.rfl
  infG_tw := fun π χ τ s h => by
    show (π.1.2 τ).map (· + (χ.1.2 τ).sum) = _
    rw [show χ.1.2 τ = {s} from h, Multiset.sum_singleton]
  csd_tw := fun π χ hχ hπ w w' h => by
    obtain ⟨c, hc⟩ := χ.exists_frobEig w
    have hc' := hχ w w' h
    rw [hc, Multiset.map_singleton] at hc'
    show ((π.1.1 w').lpChar (χ.1.1 w')).frobEig = ((π.1.1 w).lpChar (χ.1.1 w)).frobEig.map (·⁻¹)
    rw [WD.frobEig_char _ _ _ (π.2.1 w').1 (χ.2.1 w').1 hc', WD.frobEig_char _ _ _ (π.2.1 w).1 (χ.2.1 w).1 hc,
      hπ w w' h, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => (mul_inv _ _).symm
  csd_unr := fun π w w' h hc _ => ⟨(π.2.1 w').1, h w w' hc⟩
  etaT := negOneWDFam N
  etaTinv := negOneWDFam N
  etaT_unr := fun w => (lpUnr_negOne_spec N w).1
  etaT_inert := fun w _ => (lpUnr_negOne_spec N w).2.1
  etaTinv_def := fun w => ⟨(lpUnr_negOne_spec N w).1, by
    show (WD.lpUnr (h := N.plOm.2 w) {-1}).frobEig =
      (WD.lpUnr (h := N.plOm.2 w) {-1}).frobEig.map (·⁻¹)
    rw [(lpUnr_negOne_spec N w).2.1]
    simp⟩
  etaT_split := fun w w' _ _ a b ha hb => by
    have ha' : (-1 : ℂ) = a := Multiset.singleton_inj.1 ((lpUnr_negOne_spec N w).2.1.symm.trans ha)
    have hb' : (-1 : ℂ) = b := Multiset.singleton_inj.1 ((lpUnr_negOne_spec N w').2.1.symm.trans hb)
    rw [← ha', ← hb']
    norm_num
  plGw := pl
  plGw_over := h1
  plGw_inj := h2
  plGw_nconj := h3
  iotaQ := fun i => hE.elim i
  iotaQC := fun i => hE.elim i
  iota_LL := fun i => hE.elim i
  iotaQ_alg := fun i => hE.elim i
  muC := fun i => hE.elim i
  muC_csd := fun i => hE.elim i
  AV := fun i => hE.elim i
  finAV := fun i => hE.elim i
  ptV := fun i => hE.elim i
  typeV := fun i => hE.elim i
  typeV_ne := fun i => hE.elim i
  typeV_indep := fun i => hE.elim i
  typeV_top := fun i => hE.elim i
  pt_surj := fun i => hE.elim i
  eig_dim := fun i => hE.elim i
  locV := fun i => hE.elim i
  satV := fun i => hE.elim i
  locV_unr := fun i => hE.elim i
  pt_loc := fun i => hE.elim i
  infWt := fun i => hE.elim i
  locW := fun i => hE.elim i
  satW := fun i => hE.elim i
  lab_loc := fun i => hE.elim i
  wdOf := fun i => hE.elim i
  wdOf_dim := fun i => hE.elim i
  wdOf_unr := fun i => hE.elim i
  wdOf_frob := fun i => hE.elim i
  wdOf_ine := fun i => hE.elim i
  wdOf_mono0 := fun i => hE.elim i
  IsCrysW := fun i => hE.elim i
  IsPotCrysW := fun i => hE.elim i
  IsdRW := fun i => hE.elim i
  jumpsW := fun i => hE.elim i
  wdOf_unrL := fun i => hE.elim i
  wdOf_mono0L := fun i => hE.elim i
  jumpsInf := fun i => hE.elim i
  locAutHodgeTateWeightsLevelZero := fun i => hE.elim i
  jumpsInf_def := fun i => hE.elim i
  locAut_hodgeTateWeightsLevelZero_def := fun i => hE.elim i
  chi_mu := fun i => hE.elim i
  kFbar := fun i => hE.elim i

def wdTieWD (N : NData R H what₂) (hE : IsEmpty N.Loc) (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) :
    GlobalTheory.RowTie.WDTie N (nAutWD N hE pl h1 h2 h3 τ γ) :=
  ⟨fun _ => Equiv.refl _, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ _ _ => rfl⟩

end

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChart
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

section Same

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

structure SameG {y : Ys X n} (p p' : PtY ST SG Q y) : Prop where
  fr : p'.1.1.1.2 = p.1.1.1.2
  ys : p'.1.2 = p.1.2
  at_eq : ∀ w : SG, p'.1.1.deco.1.at w.1 = p.1.1.deco.1.at w.1
  be : p'.1.1.deco.1.be = p.1.1.deco.1.be

theorem SameG.refl {y : Ys X n} (p : PtY ST SG Q y) : SameG p p :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

private theorem locP_gmap_eq_of_locP_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (g : Sp E n ≃ₗ[E] Sp E n) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N') = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N) := by
  have hs : ∀ (s : 𝓞 E) (z : Sp E n), g.symm (s • z) = s • g.symm z := fun s z =>
    ((g.symm : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s z
  have hmemL : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ M := fun _ _ => Iff.rfl

  have hmemg : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g M) ↔ g.symm x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := by
    intro M x
    rw [hmemL, hmemL]
    constructor
    · rintro ⟨s, hs0, hx⟩
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
      have hz' : z = g.symm (s • x) := by
        rw [← hzx]
        simp
      exact ⟨s, hs0, by rw [← hs, ← hz']; exact hz⟩
    · rintro ⟨s, hs0, hx⟩
      refine ⟨s, hs0, Submodule.mem_map.mpr ⟨g.symm (s • x), by rw [hs]; exact hx, by simp⟩⟩
  ext x
  rw [hmemg, hmemg, h]

theorem SameG.smul {y : Ys X n} {Λ : LevFam X.E X.K n SG} {Θ : LevQFam X.E X.K n Q} (h : FrmG Λ Θ) {p p' : PtY ST SG Q y}
    (r : SameG p p') : SameG ((ptYAct y Λ Θ).toSMul.smul h p) ((ptYAct y Λ Θ).toSMul.smul h p') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg (fun F => fun P => (FrmG.incl Λ Θ h).1.1 * F P * ((FrmG.incl Λ Θ h).2.2 P)⁻¹.1) r.fr
  · exact congrArg (fun S => (fun v => h.1.1 v) '' S) r.ys
  · intro w
    show Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p'.1.1.deco.1.N) =
      Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p.1.1.deco.1.N)
    exact locP_gmap_eq_of_locP_eq w.1 h.1.1 (r.at_eq w)
  · exact congrArg (fun B => fun w x => ((FrmG.incl Λ Θ h).2.1 w).1.mulVec (B w (h.1.1.symm x))) r.be

theorem SameG.dn {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) :
    SameG p (p.mv (p.1.1.deco.dn P f')) := by
  classical
  unfold PtY.mv
  refine Eq.mpr (apply_dite (SameG p) _ _ _) ?_
  split
  · refine ⟨rfl, rfl, fun w => ?_, ?_⟩
    · show (p.1.1.deco.dn P f').1.at w.1 = p.1.1.deco.1.at w.1
      unfold DecoSet.dn
      split_ifs with hok
      · exact ((p.1.1.deco.2.dnN_spec P hP.ne).2.2.1 w.1 (hP.sg w).1 (hP.sg w).2).localization_eq
      · rfl
    · show (p.1.1.deco.dn P f').1.be = p.1.1.deco.1.be
      unfold DecoSet.dn
      split_ifs <;> rfl
  · exact SameG.refl p

end Same

section Coset

private theorem cosetIn_eq_of_sameG' {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q := by
  have hfr : ∀ P, frsF sel mu q'.1.1 P = frsF sel mu q.1.1 P := by
    intro P
    unfold frsF
    split_ifs with hP
    · unfold Deco.liftFr
      rw [r.at_eq ⟨P.1, hP⟩, r.be]
    · exact congrFun r.fr _
  funext P
  unfold cosetIn
  rw [r.ys, hfr P]


open Classical GlobalTheory.TopStep in
theorem cosetIn_eq_of_sameG {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (hX : X.Ok) (hPr : Pr.Ok)
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q :=
  cosetIn_eq_of_sameG' r

end Coset

section Normal

theorem prefRep_pref {G D : Type} [Group G] [MulAction G D] (pref : D → Prop) (q : MulAction.orbitRel.Quotient G D)
    (h : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = q ∧ pref p) : pref (prefRep pref q) := by
  unfold prefRep
  rw [dite_eq_left h]
  exact h.choose_spec.2

theorem GStep.NormalFor.eq {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} {b : S.β} {f : S.D b → A}
    {q q' : S.D b} (hq : S.NormalFor b f q) (hq' : S.NormalFor b f q')
    (h : ∀ r, (∃ g : S.G b, r = f (g • q)) ↔ ∃ g : S.G b, r = f (g • q')) : f q = f q' := by
  unfold GStep.NormalFor at hq hq'
  rw [hq, hq']
  exact congrArg (@Classical.epsilon A ⟨f q⟩) (funext fun r => propext (h r))

theorem GStep.exists_normalFor {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (q : S.D b) : ∃ g : S.G b, S.NormalFor b f (g • q) := by
  have hex : ∃ r, ∃ g : S.G b, r = f (g • q) := ⟨f q, 1, by rw [one_smul]⟩
  obtain ⟨g, hg⟩ := Classical.epsilon_spec hex
  refine ⟨g, ?_⟩
  have hset : (fun r => ∃ g : S.G b, r = f (g • q)) = (fun r => ∃ g' : S.G b, r = f (g' • g • q)) := by
    funext r
    apply propext
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g, by rw [mul_smul]⟩
  unfold GStep.NormalFor
  exact hg.symm.trans (congrArg (@Classical.epsilon A ⟨f q⟩) hset)

theorem GStep.prefRep_eq_of_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hn : ∀ q : MulAction.orbitRel.Quotient (S.G b) (S.D b), S.NormalFor b f (prefRep pf q)) (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) (d' : S.D b)
    (hd : ∀ h : S.G b, f (h • d') = f (h • prefRep pf q)) :
    f (prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d')) = f (prefRep pf q) := by
  obtain ⟨k, hk⟩ : ∃ k : S.G b, k • d' = prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d') :=
    Quotient.exact (prefRep_spec pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d'))
  refine GStep.NormalFor.eq (hn _) (hn q) fun r => ⟨?_, ?_⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k, by rw [← hk, ← mul_smul, hd]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k⁻¹, by rw [← hd, ← hk, mul_smul, inv_smul_smul]⟩

theorem GStep.prefRep_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hpf : ∀ p, pf p → S.NormalFor b f p) (hnp : ∀ p, S.NormalFor b f p → pf p)
    (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) : S.NormalFor b f (prefRep pf q) := by
  obtain ⟨g, hg⟩ := GStep.exists_normalFor S b f (Quotient.out q)
  have hex : ∃ p, Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) p = q ∧ pf p :=
    ⟨g • Quotient.out q, (Quotient.sound (s := MulAction.orbitRel (S.G b) (S.D b)) (MulAction.mem_orbit _ g)).trans
      (Quotient.out_eq q), hnp _ hg⟩
  exact hpf _ (prefRep_pref pf q hex)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem TC.pref_of_normalFor (u : B.Word) (a : I.ι) (j : ℕ) (hj : j + 1 = B.R.m) (b : (I.stp0 u a j).β) (p : (I.stp0 u a j).D b)
    (h : (I.stp0 u a j).NormalFor b (fun q' : (I.stp0 u a j).D b => cosetIn q') p) : I.pref u a j b p := by
  have hm := B.R.two_le_m
  refine ⟨fun h0 => absurd hj (by omega), fun _ => h, ?_⟩
  show ∀ h : j = B.R.m, _
  intro hjm
  exact absurd hjm (by omega)

private theorem TC.cosetIn_rep_cl_dn_eq (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (v : (B.primes X).vT u)
    (c : (I.stp u a i).Cl) (f : Sp B.fields.E (B.R.N i) → Res v.1) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (((I.atIn u a).A i).dn c.1 ((I.stp u a i).rep c) v f))) =
      cosetIn ((I.stp u a i).rep c) := by
  obtain ⟨b, q⟩ := c
  have r0 : SameG ((I.stp u a i).rep ⟨b, q⟩) (((I.atIn u a).A i).dn b ((I.stp u a i).rep ⟨b, q⟩) v f) :=
    SameG.dn _ v (moveHyp_of_ok hPr u v) f
  by_cases hi : i + 1 = B.R.m
  · exact GStep.prefRep_eq_of_normal (I.stp0 u a i) b (fun q' => cosetIn q') (I.pref u a i b)
      (GStep.prefRep_normal (I.stp0 u a i) b _ (I.pref u a i b) (fun p hp => hp.2.1 hi)
        (fun p hp => I.pref_of_normalFor u a i hi b p hp)) q _
      (fun h => cosetIn_eq_of_sameG' (SameG.smul h r0))
  ·
    have hemp : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u i, cosetIn p = fun _ => ∅ := by
      intro p
      have hys : ∀ (Y : Set (Sp B.fields.E (B.R.N i))) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))),
          Y ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) i).ys N → Y = ∅ := by
        intro Y N hY
        unfold ysAt at hY
        rw [if_neg hi] at hY
        exact hY
      have hp : p.1.2 = ∅ := hys _ _ p.2
      funext P
      unfold cosetIn
      rw [hp]
      ext z
      simp
    exact (hemp _).trans (hemp _).symm

end Normal

theorem TC.dn_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  intro B X I _ _ l Z u a i hi bad Ch chOf K eY eV L hK _ _ _ v β c g _

  obtain ⟨k, hR⟩ := hK
  exact ((hR.key ((I.fm l u a).dn i v c.1 g) c.1).mpr ⟨rfl, I.cosetIn_rep_cl_dn_eq l.pr u a i v c.1 _⟩).trans c.2

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChartStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_down_level_prime_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
  exact GlobalTheory.Mem.Col2.TC.dn_keeps_chart I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimesOverPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

theorem conjO_piG_ne (hPr : Pr.Ok) (a : Fin 2) : X.conjO (Pr.piG a) ≠ 0 := by
  intro h0
  have := hPr.piG_norm a
  rw [h0, mul_zero] at this
  exact (Nat.cast_ne_zero.2 (hPr.g_prime a).ne_zero) this.symm

theorem mem_vG_iff (hPr : Pr.Ok) (a : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ Pr.vG a ↔ X.conjO (Pr.piG a) ∈ P.asIdeal := mem_divs (conjO_piG_ne hPr a) P

theorem g_mem_of_isOver {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)}
    (hv : IsOver v P) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ((Pr.g a : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [hv, Ideal.mem_comap, map_natCast] at h
  exact h

theorem eq_of_isOver (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) {P Q : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) (hQ : Q ∈ Pr.vGs)
    (hPv : IsOver v P) (hQv : IsOver v Q) : Q = P := by
  rcases rll_over_cases hc hPv hQv with e | e
  · exact e
  exfalso
  have hPa := mem_vG_of_g_mem hPr hP (g_mem_of_isOver hPv h)
  have hQa := mem_vG_of_g_mem hPr hQ (g_mem_of_isOver hQv h)
  rw [mem_vG_iff hPr] at hPa hQa
  rw [e, mem_conjP] at hQa
  have h2 : cO X.E (X.conjO (Pr.piG a)) = Pr.piG a := RingOfIntegers.ext (star_star _)
  rw [h2] at hQa
  obtain ⟨x, y, hxy⟩ := hPr.piG_cop a
  refine P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ hQa) (Ideal.mul_mem_left _ _ hPa)

theorem exists_over_vGs (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ∃ w : {w // w ∈ Pr.vGs}, IsOver v w.1 := by
  have h01 : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
  have hv : v ∈ plUnder X.F Pr.vGs := by
    rw [plUnder_vGs hc hPr v]
    rcases h01 a with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨P, hP, hPv⟩ := hv
  exact ⟨⟨P, hP⟩, hPv⟩

theorem isOver_of_under {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : P.under (𝓞 X.F) = v) :
    IsOver v P := by
  subst h
  rfl

theorem under_of_isOver {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : IsOver v P) :
    P.under (𝓞 X.F) = v :=
  HeightOneSpectrum.ext h.symm

end GlobalTheory.Mem.TypePrimes

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

theorem residue_natCast (hPr : Pr.Ok) {a : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG a)
    (c : 𝓞 X.E ⧸ w.asIdeal) : ∃ k : ℕ, c = k := by
  haveI : NeZero (Pr.g a) := ⟨(hPr.g_prime a).ne_zero⟩
  have e := (nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime a) (by
    rw [← hPr.vG_norm a w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some
  exact ⟨(e.symm c).val, by rw [← map_natCast e, ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply]⟩

theorem vG_disjoint (hPr : Pr.Ok) : Disjoint (Pr.vG 0) (Pr.vG 1) := by
  rw [Finset.disjoint_left]
  intro w h0 h1
  have hc : IsCoprime ((Pr.g 0 : ℕ) : 𝓞 X.E) ((Pr.g 1 : ℕ) : 𝓞 X.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime 0) (hPr.g_prime 1)).2 hPr.g_ne)
  obtain ⟨x, y, hxy⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h0)) (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h1))

theorem primes_over_places : ∀ (X : Fields) (Pr : Primes X) (hc : Formalism.BasicNotions.CMData X.F X.E), Pr.Ok →
    ∃ wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs},
      (∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h) ∧
      (∀ a v h, (∀ P : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = v → X.conjO (Pr.piG a) ∈ P.asIdeal →
          P = (wOf a v h).1) ∧ (wOf a v h).1.under (𝓞 X.F) = v ∧
        ∀ c : 𝓞 X.E ⧸ (wOf a v h).1.asIdeal, ∃ k : ℕ, c = k) ∧
      ∀ φ : {w // w ∈ Pr.vGs} → ℂ, ∏ w, φ w =
        ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) := by
  intro X Pr hc hPr
  classical
  let wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs} :=
    fun a v h => (exists_over_vGs hc hPr h).choose
  have hspec : ∀ a v h, IsOver v (wOf a v h).1 := fun a v h => (exists_over_vGs hc hPr h).choose_spec
  have h1 : ∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h := by
    intro a v h w
    constructor
    · intro hw
      exact Subtype.ext (eq_of_isOver hc hPr h (wOf a v h).2 w.2 (hspec a v h) hw)
    · rintro rfl
      exact hspec a v h
  have hin : ∀ a v h, (wOf a v h).1 ∈ Pr.vG a := fun a v h =>
    mem_vG_of_g_mem hPr (wOf a v h).2 (g_mem_of_isOver (hspec a v h) h)
  refine ⟨wOf, h1, fun a v h => ⟨?_, under_of_isOver (hspec a v h), residue_natCast hPr (hin a v h)⟩, ?_⟩
  · intro P hPu hP
    have hPa : P ∈ Pr.vG a := (mem_vG_iff hPr a P).2 hP
    exact eq_of_isOver hc hPr h (wOf a v h).2 (mem_vGs hPa) (hspec a v h) (isOver_of_under hPu)
  · intro φ
    let φ' : HeightOneSpectrum (𝓞 X.E) → ℂ := fun w => if hw : w ∈ Pr.vGs then φ ⟨w, hw⟩ else 1
    have hL : ∏ w, φ w = ∏ w ∈ Pr.vGs, φ' w := by
      rw [← Finset.prod_coe_sort Pr.vGs φ']
      refine Finset.prod_congr rfl fun w _ => ?_
      simp only [φ', dif_pos w.2]
    have hA : ∀ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) =
        ∏ w ∈ Pr.vG a, φ' w := by
      intro a
      let f : HeightOneSpectrum (𝓞 X.F) → ℂ := fun v => if h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal then φ (wOf a v h) else 1
      have e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h)) = ∏ᶠ v, f v := by
        refine finprod_congr fun v => ?_
        exact finprod_eq_dif _
      have hsupp : Function.mulSupport f ⊆ ((Pr.vG a).image fun w => w.under (𝓞 X.F) : Finset _) := by
        intro v hv
        have h' : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal := by
          by_contra hn
          exact hv (by simp only [f, dif_neg hn])
        rw [Finset.coe_image]
        exact ⟨(wOf a v h').1, hin a v h', under_of_isOver (hspec a v h')⟩
      rw [e1, finprod_eq_prod_of_mulSupport_subset f hsupp, Finset.prod_image]
      · refine Finset.prod_congr rfl fun w hw => ?_
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        have hw' : w ∈ Pr.vGs := mem_vGs hw
        have e2 : wOf a (w.under (𝓞 X.F)) hg = ⟨w, hw'⟩ :=
          ((h1 a _ hg ⟨w, hw'⟩).1 (isOver_of_under rfl)).symm
        simp only [f, φ', dif_pos hg, dif_pos hw', e2]
      · intro w hw w' hw' he
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        exact (eq_of_isOver hc hPr hg (mem_vGs hw) (mem_vGs hw') (isOver_of_under rfl) (isOver_of_under he.symm)).symm
    rw [hL, Fin.prod_univ_two, hA 0, hA 1]
    unfold Primes.vGs
    exact Finset.prod_union (vG_disjoint hPr)

end GlobalTheory.Mem.TypePrimes
end
