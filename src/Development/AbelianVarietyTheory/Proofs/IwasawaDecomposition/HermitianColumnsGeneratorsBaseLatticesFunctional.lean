module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroLevelTypePrimeOrientationFramesFunctiona

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelFunctionalsIntermediateStepsTrueColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelFunctionalsIntermediateStepsTrueColumn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TC.FvChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (J.reindex (finCongr h) (finCongr h)) (fun j => x ((finCongr h).symm j))
      (fun j => y ((finCongr h).symm j)) = hform σ J x y := by
  subst h
  simp [hform]

theorem mem_latS_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E)
    (Lb : Submodule (𝓞 E) (Fin a → E)) (w : HeightOneSpectrum (𝓞 F)) (t : Fin a → E ⊗[F] w.adicCompletion F)
    (ht : t ∈ latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J Lb))) :
    (fun j => t ((finCongr h).symm j)) ∈ latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet σ (J.reindex (finCongr h) (finCongr h)) (reL h Lb))) := by
  subst h
  have hL : reL rfl Lb = Lb := by
    ext x
    simp [reL, reV]
  simpa [hL] using ht

theorem reGL_solve {a b : ℕ} (h : a = b) (w : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g' : GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hg' : g' = reGL h _ g) (t : Fin a → E ⊗[F] w.adicCompletion F) (z : Fin a → E)
    (ht : (bc (prV (E := E) w) g).1 *ᵥ t = fun j => inclE (F := F) (w.adicCompletion F) (z j)) :
    ((bc (prV (E := E) w) g')⁻¹).1 *ᵥ
      (fun j => inclE (F := F) (w.adicCompletion F) (z ((finCongr h).symm j))) =
      fun j => t ((finCongr h).symm j) := by
  subst h hg'
  have hg : reGL rfl _ g = g := by
    ext
    simp [reGL]
  simp only [hg, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]
  rw [← ht, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart

theorem crdN_mem_LdG (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ LdG D i hi (clsCrd D u i hi c) := by
  apply Submodule.subset_span
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have h2 := hform_reindex (rankN D i hi) (sigD D : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd (D.sp.X i) y) (Formalism.L2.Herm.crd (D.sp.X i) z.1)
  have h3 := Formalism.L2.Herm.hT_crd D.sp.cm (D.sp.X i) y z.1
  have hz := z.2
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hz
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hz y hy)
  refine ⟨r, ?_⟩
  change _ = hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
    (fun j => Formalism.L2.Herm.crd (D.sp.X i) y ((finCongr (rankN D i hi)).symm j))
    (fun j => Formalism.L2.Herm.crd (D.sp.X i) z.1 ((finCongr (rankN D i hi)).symm j))
  unfold gramN
  rw [h2]
  rw [hr]
  exact h3

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart

theorem exists_reindex_hom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : J' = J.reindex (finCongr h) (finCongr h))
    (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E)) (hL : Lb' = reL h Lb)
    (w : HeightOneSpectrum (𝓞 F)) :
    ∃ tr : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J Lb)) →+
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J' Lb')),
      ∀ t, (tr t).1 = fun j => t.1 ((finCongr h).symm j) := by
  subst hJ hL
  exact ⟨{ toFun := fun t => ⟨fun j => t.1 ((finCongr h).symm j), mem_latS_reindex h σ J Lb w t.1 t.2⟩
           map_zero' := rfl
           map_add' := fun _ _ => rfl }, fun _ => rfl⟩

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart


set_option maxHeartbeats 1000000 in
theorem fvTie_of_car {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A)
    (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u i) :
    Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb
      (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => D.clsLat u i c.1) (H.vT u v).1 ((D.mem u).A.Fv v)
      (fun c z => (D.fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  have hc := hH.carC u i h1 h2 β
  have hw : (H.vT u v).1 = ((F u).atT.eV v).1 := congrArg (fun e => (e v).1) (hH.eV u).symm
  suffices hs : ∀ w, w = ((F u).atT.eV v).1 →
      Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb
        (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => D.clsLat u i c.1) w ((D.mem u).A.Fv v)
        (fun c z => (D.fm u).fv i v c.1 ((A u).pr i v c.1 z))) from hs _ hw
  intro w hw'
  subst hw'
  obtain ⟨tr, htr⟩ := exists_reindex_hom (F := D.host.F) (rankN D i (le_of_succ_m h2))
    (sigD D : D.host.E →+* D.host.E) (D.sp.X i).gram (gramN D i (le_of_succ_m h2)) rfl
    (H.lev u i h1 (le_of_succ_m h2) β).Lb ((F u).ch i h1 h2 β).lev.Lb hc.Lb_eq ((F u).atT.eV v).1
  refine ⟨⟨((F u).fMeC i h1 h2 β v).toAddMonoidHom.comp
    ((((F u).ch i h1 h2 β).lev.fT ((F u).atT.eV v).1 ((F u).atT.eV v).2).toAddMonoidHom.comp tr), ?_⟩⟩
  intro c z t ht
  have hmem := crdN_mem_LdG D u i (le_of_succ_m h2) c.1 z
  have hp := hT.prC u i h1 h2 v c.1 z ⟨_, hmem⟩ rfl
  refine (congrArg ((D.fm u).fv i v c.1) hp).symm.trans ?_
  have key : ((bc (prV (E := D.host.E) ((F u).atT.eV v).1) (((F u).ch i h1 h2 β).y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F)
        (crdN D i (le_of_succ_m h2) z.1 a)) = (tr t).1 :=
    (reGL_solve (rankN D i (le_of_succ_m h2)) ((F u).atT.eV v).1 ((H.cls u i h1 (le_of_succ_m h2) β).y c).1
      (((F u).ch i h1 h2 β).y c).1 (hc.y_eq c) t.1 (Formalism.L2.Herm.crd (D.sp.X i) z.1) ht).trans (htr t).symm
  have hz := (congrArg (fun x => x ∈ latS (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F)
    (intV D.host.E ((F u).atT.eV v).1)
    (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E)
      (gramN D i (le_of_succ_m h2)) ((F u).ch i h1 h2 β).lev.Lb))) key).mpr (tr t).2
  refine ((F u).fvC i h1 h2 v β c ⟨_, hmem⟩ hz).trans ?_
  exact congrArg (fun x => ((F u).fMeC i h1 h2 β v)
    ((((F u).ch i h1 h2 β).lev.fT ((F u).atT.eV v).1 ((F u).atT.eV v).2) x)) (Subtype.ext key)

end GlobalTheory.Mem.Col2.TC.FvChart


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TC.fvTie_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u i), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => (I.rec7 l Z).clsLat u i c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  intro B X I _ _ l Z H F A _ hH hT u i h1 h2 v β
  exact FvChart.fvTie_of_car H F A hH hT u i h1 h2 v β
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelFunctionalsIntermediateStepsTrueColumnStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevelFunctionals_intermediateSteps_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u i), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => (I.rec7 l Z).clsLat u i c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  first | exact @GlobalTheory.Mem.Col2.TC.fvTie_charts | exact GlobalTheory.Mem.Col2.TC.fvTie_charts | (intros; apply GlobalTheory.Mem.Col2.TC.fvTie_charts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartBaseLatticeSupDualSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartBaseLatticeSupDualSelfDual
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.ChartBase

open NumberField

variable {E : Type} [Field E] [NumberField E]

theorem hform_one (σ : E →+* E) {n : ℕ} (x y : Fin n → E) :
    Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold Formalism.UG.hform
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.one_apply]

theorem sig_int (σ : E →+* E) (s : 𝓞 E) : σ (s : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨RingOfIntegers.mapRingHom σ s, rfl⟩

theorem sup_dual_eq (σ : E →+* E) {n : ℕ} (t pb : 𝓞 E) (ht : (t : E) ≠ 0) (hpb : (pb : E) = σ t)
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = r ∧ (j.1 + 1 = n → t ∣ r))
    (M : Submodule (𝓞 E) (Fin n → E))
    (hM : ∀ x, x ∈ M ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range) :
    Λ ⊔ Ideal.span {pb} • Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) Λ) = M := by
  classical
  have hσt : σ (t : E) ≠ 0 := (map_ne_zero σ).2 ht
  have hpb0 : (pb : E) ≠ 0 := by rw [hpb]; exact hσt
  apply le_antisymm
  · refine sup_le (fun x hx => (hM x).2 fun j => ?_) ?_
    · obtain ⟨r, hr, -⟩ := (hΛ x).1 hx j
      exact ⟨r, hr.symm⟩
    ·
      have key : ∀ y ∈ Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) Λ), pb • y ∈ M := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          refine (hM _).2 fun j => ?_
          have hs : ∀ c : 𝓞 E, (∀ j' : Fin n, j'.1 + 1 = n → t ∣ (if j' = j then c else 0)) →
              Pi.single j (c : E) ∈ Λ := by
            intro c hc
            refine (hΛ _).2 fun j' => ⟨if j' = j then c else 0, ?_, hc j'⟩
            by_cases h : j' = j
            · subst h; simp
            · simp [h, Pi.single_apply]
          have hval : ∀ c : 𝓞 E, Pi.single j (c : E) ∈ Λ → σ (c : E) * y j ∈ (algebraMap (𝓞 E) E).range := by
            intro c hc
            have := hy _ hc
            rw [hform_one] at this
            rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)] at this
            simpa using this
          show ((pb • y) j) ∈ _
          rw [Pi.smul_apply, Algebra.smul_def]
          by_cases hj : j.1 + 1 = n
          · have h1 := hval t (hs t fun j' _ => by split_ifs <;> simp)
            rw [show algebraMap (𝓞 E) E pb = (pb : E) from rfl, hpb]
            exact h1
          · have h1 := hval 1 (hs 1 fun j' hj' => by
              split_ifs with h
              · subst h; exact absurd hj' hj
              · simp)
            have h1' : y j ∈ (algebraMap (𝓞 E) E).range := by simpa using h1
            obtain ⟨a, ha⟩ := h1'
            exact ⟨pb * a, by rw [map_mul, ha]⟩
        | zero => simpa using M.zero_mem
        | add a b _ _ ha hb => rw [smul_add]; exact M.add_mem ha hb
        | smul c a _ ha => rw [smul_comm]; exact M.smul_mem c ha
      refine Submodule.smul_le.2 fun r hr y hy => ?_
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [mul_smul]
      exact M.smul_mem a (key y hy)
  · intro x hx
    have hx' := (hM x).1 hx
    let x1 : Fin n → E := fun j => if j.1 + 1 = n then 0 else x j
    let z : Fin n → E := fun j => if j.1 + 1 = n then x j / (pb : E) else 0
    have hsplit : x = x1 + pb • z := by
      funext j
      simp only [x1, z, Pi.add_apply, Pi.smul_apply, Algebra.smul_def]
      split_ifs
      · rw [show algebraMap (𝓞 E) E pb = (pb : E) from rfl]; field_simp; ring
      · simp
    rw [hsplit]
    refine Submodule.add_mem_sup ?_ ?_
    · refine (hΛ _).2 fun j => ?_
      by_cases hj : j.1 + 1 = n
      · exact ⟨0, by simp [x1, hj], fun _ => dvd_zero _⟩
      · obtain ⟨r, hr⟩ := hx' j
        exact ⟨r, by simp [x1, hj, hr], fun h => absurd h hj⟩
    · refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self pb) (Submodule.subset_span ?_)
      intro x0 hx0
      rw [hform_one]
      refine Subring.sum_mem _ fun i _ => ?_
      by_cases hi : i.1 + 1 = n
      · obtain ⟨r, hr, hd⟩ := (hΛ x0).1 hx0 i
        obtain ⟨s, rfl⟩ := hd hi
        obtain ⟨a, ha⟩ := hx' i
        simp only [z, hi, if_true, hr]
        have e : σ ((t * s : 𝓞 E) : E) * (x i / (pb : E)) = σ (s : E) * x i := by
          rw [hpb]; push_cast; rw [map_mul]; field_simp
        rw [e, ← ha]
        obtain ⟨b, hb⟩ := sig_int σ s
        exact ⟨b * a, by rw [map_mul, hb]⟩
      · simp only [z, hi, if_false, mul_zero]
        exact Subring.zero_mem _

end GlobalTheory.Mem.Col2.TC.ChartBase

namespace GlobalTheory.Mem.Col2.TC.ChartBase

open NumberField

variable {E : Type} [Field E] [NumberField E]

theorem mem_reL_iff {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin a → E)) (x : Fin a → E) :
    x ∈ L ↔ Formalism.L2.Forms.reV h E x ∈ Formalism.L2.Forms.reL h L := by
  subst h
  have e : ∀ y : Fin a → E, Formalism.L2.Forms.reV rfl E y = y := fun y => by
    funext j; simp [Formalism.L2.Forms.reV]
  constructor
  · intro hx; exact Submodule.mem_map.2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
    have : y = x := by
      have := hyx
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, e] at this
      exact this
    exact this ▸ hy

theorem reV_apply {a b : ℕ} (h : a = b) (x : Fin a → E) (j : Fin b) :
    Formalism.L2.Forms.reV h E x j = x (Fin.cast h.symm j) := by
  subst h; simp [Formalism.L2.Forms.reV]

end GlobalTheory.Mem.Col2.TC.ChartBase

namespace GlobalTheory.Mem.Col2.TC.ChartBase

theorem mem_of_baseL {B : Base} {a b : ℕ} (h : a = b) (t : 𝓞 B.host.E) (L : Submodule (𝓞 B.host.E) (Fin a → B.host.E))
    (L' : Submodule (𝓞 B.host.E) (Fin b → B.host.E)) (hL' : L' = Formalism.L2.Forms.reL h L)
    (hb : ∀ x, x ∈ L' ↔ x ∈ baseL B b t) (x : Fin a → B.host.E) :
    x ∈ L ↔ ∀ j : Fin a, ∃ r : 𝓞 B.host.E, x j = r ∧ (j.1 + 1 = a → t ∣ r) := by
  rw [mem_reL_iff h L x, ← hL', hb]
  unfold baseL
  simp only [Set.mem_setOf_eq, reV_apply]
  constructor
  · intro H j
    obtain ⟨r, hr, hd⟩ := H (Fin.cast h j)
    exact ⟨r, by simpa using hr, fun hj => hd (by simp [← h, hj])⟩
  · intro H j
    obtain ⟨r, hr, hd⟩ := H (Fin.cast h.symm j)
    exact ⟨r, hr, fun hj => hd (by simp [h, hj])⟩

end GlobalTheory.Mem.Col2.TC.ChartBase


open GlobalTheory.Mem.Col2.TC.ChartBase in
theorem GlobalTheory.Mem.Col2.TC.chart_base_sup_dual : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), (H.lev u i h1 hm β).Lb ⊔ Ideal.span {pb} • Formalism.L2.Herm.dualL (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 hm β).Lb = Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0 := by
  intro B X I hOk hP l Z H F A hS hH hT u pb hpb i h1 hm β
  have hC := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hP l Z
  obtain ⟨hG, hL0, -⟩ := hC.2.2.2 i hm

  have hG1 : ((I.rec7 l Z).sp.X i).gram = 1 := by
    ext a b
    have := congrFun (congrFun hG (finCongr (rankN (I.rec7 l Z) i hm) a)) (finCongr (rankN (I.rec7 l Z) i hm) b)
    simpa [gramN, Matrix.one_apply] using this

  have hσ : ∀ x : (I.rec7 l Z).host.E, ((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) x = (I.rec7 l Z).host.conj x := fun x => by
    have := (I.rec7 l Z).host.isCMField_hostE
    exact (I.rec7 l Z).host.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ (I.rec7 l Z).host.φ₀ x).trans
      ((I.rec7 l Z).host.conjE_apply (I.rec7 l Z).host.φ₀ x).symm)

  have hpi : (A u).piU = X.piT u := (hT.piU u).symm.trans (hS u).1.piU
  have hT0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h0 => by
    have e := X.piT_norm u
    rw [h0, zero_mul] at e
    exact (B.T_prime u).ne_zero (by exact_mod_cast e.symm)

  have hM : ∀ x, x ∈ Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0 ↔ ∀ j, x j ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range := by
    intro x
    rw [mem_reL_iff (rankN (I.rec7 l Z) i hm) _ x]
    have e : Formalism.L2.Forms.reL (rankN (I.rec7 l Z) i hm)
        (Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0) = selfDualLatticeCoords (I.rec7 l Z) i hm := by
      unfold Formalism.L2.Forms.reL Formalism.L2.Herm.crdLat
      rw [← Submodule.map_comp]; rfl
    rw [e, hL0]
    simp only [reV_apply]
    constructor
    · intro H j
      have h' := H (Fin.cast (rankN (I.rec7 l Z) i hm) j)
      rwa [Fin.cast_cast, Fin.cast_eq_self] at h'
    · intro H j; exact H _

  have hΛ : ∀ x, x ∈ (H.lev u i h1 hm β).Lb ↔ ∀ j : Fin ((I.rec7 l Z).sp.X i).rank, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = r ∧
      (j.1 + 1 = ((I.rec7 l Z).sp.X i).rank → X.piT u ∣ r) := by
    rcases Nat.lt_or_ge i (I.rec7 l Z).R.m with hlt | hge
    · have h2 : i + 1 ≤ (I.rec7 l Z).R.m := hlt
      have hc := hH.carC u i h1 h2 β
      obtain ⟨k, hk⟩ := (hS u).1.mid i h1 h2
      exact mem_of_baseL (rankN (I.rec7 l Z) i (le_of_succ_m h2)) (X.piT u) _ _ hc.Lb_eq (hk.lb β)
    · obtain rfl : i = (I.rec7 l Z).R.m := le_antisymm hm hge
      obtain rfl : β = chM H u := @Unique.eq_default _ (H.Ch_m u).some β
      have hc := hH.carM u
      obtain ⟨k, hk⟩ := (hS u).1.ends _ le_rfl (Or.inr rfl)
      exact mem_of_baseL (rankN (I.rec7 l Z) _ le_rfl) (X.piT u) _ _ hc.Lb_eq (hk.lb ())
  unfold Formalism.L2.Herm.dualL
  rw [hG1]
  exact sup_dual_eq _ (X.piT u) pb hT0 (by
    have e := hσ ((X.piT u : 𝓞 B.host.E) : B.host.E)
    rw [hpi] at hpb
    exact hpb.trans e.symm) _ hΛ _ hM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartBaseLatticeSupDualSelfDualStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_base_lattice_sup_dual_selfDual : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), (H.lev u i h1 hm β).Lb ⊔ Ideal.span {pb} • Formalism.L2.Herm.dualL (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 hm β).Lb = Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.chart_base_sup_dual | exact GlobalTheory.Mem.Col2.TC.chart_base_sup_dual | (intros; apply GlobalTheory.Mem.Col2.TC.chart_base_sup_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLatticeStepZeroAddConjGeneratorDualSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLatticeStepZeroAddConjGeneratorDualSelfDual
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem base_sup_dual_eq {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n : ℕ}
    (Lb M : Submodule (𝓞 E) (Fin n → E)) (π pb : 𝓞 E) (hpb : (pb : E) = σ (π : E))
    (hspan : Submodule.span E (Lb : Set (Fin n → E)) = ⊤)
    (hL : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    (hM : ∀ x, x ∈ M ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range) :
    Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 E) (dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb) = M := by
  have hform1 : ∀ x y : Fin n → E, hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
    intro x y
    unfold hform
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  have hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range := fun r =>
    ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      refine (hM x).2 fun j => ?_
      obtain ⟨r, hr, -⟩ := (hL x).1 hx j
      exact ⟨r, hr.symm⟩
    · rw [Submodule.ideal_span_singleton_smul]
      rintro _ ⟨y, hy, rfl⟩
      simp only [DistribSMul.toLinearMap_apply]
      induction hy using Submodule.span_induction with
      | mem y hy =>
        refine (hM _).2 fun j => ?_
        by_cases hj : j.1 + 1 = n
        · have hx : Pi.single j (π : E) ∈ Lb := by
            refine (hL _).2 fun i => ?_
            by_cases h : i = j
            · subst h
              exact ⟨π, by simp, fun _ => dvd_rfl⟩
            · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
          have := hy _ hx
          rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
          simpa [Algebra.smul_def, hpb] using this
        · have hx : Pi.single j (1 : E) ∈ Lb := by
            refine (hL _).2 fun i => ?_
            by_cases h : i = j
            · subst h
              exact ⟨1, by simp, fun hi => absurd hi hj⟩
            · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
          have := hy _ hx
          rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
          simp only [Pi.single_eq_same, map_one, one_mul] at this
          obtain ⟨r, hr⟩ := this
          exact ⟨pb * r, by simp [Algebra.smul_def, hr]⟩
      | zero => simp
      | add y z _ _ h1 h2 => rw [smul_add]; exact M.add_mem h1 h2
      | smul c y _ h => rw [smul_comm]; exact M.smul_mem c h
  · intro x hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (le_sup_left : Lb ≤ _) ((hL x).2 fun j => j.elim0)
    have hxi := (hM x).1 hx
    let l : Fin n := ⟨n - 1, by omega⟩
    have hl : l.1 + 1 = n := by simp [l]; omega
    have hπ : π ≠ 0 := by
      rintro rfl
      have hle : Submodule.span E (Lb : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) l) := by
        refine Submodule.span_le.2 fun z hz => ?_
        obtain ⟨r, hr, hd⟩ := (hL z).1 hz l
        have : r = 0 := zero_dvd_iff.1 (hd hl)
        simp [hr, this]
      rw [hspan] at hle
      have := hle (Submodule.mem_top (x := Pi.single l (1 : E)))
      simp at this
    have hpb0 : (pb : E) ≠ 0 := by
      rw [hpb]
      intro h
      exact hπ (by simpa using (map_eq_zero σ).1 h)
    obtain ⟨t, ht⟩ := hxi l
    have hy : Pi.single l (x l / (pb : E)) ∈ dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb := by
      intro z hz
      rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)]
      obtain ⟨r, hr, hd⟩ := (hL z).1 hz l
      obtain ⟨s, rfl⟩ := hd hl
      obtain ⟨w, hw⟩ := hσO s
      refine ⟨w * t, ?_⟩
      rw [map_mul, hw, ht, hr, Pi.single_eq_same]
      simp only [map_mul, ← hpb]
      rw [← ht]
      field_simp
    have hx' : Function.update x l 0 ∈ Lb := by
      refine (hL _).2 fun j => ?_
      by_cases h : j = l
      · subst h
        exact ⟨0, by simp, fun _ => dvd_zero _⟩
      · obtain ⟨r, hr⟩ := hxi j
        refine ⟨r, by simp [h, hr], fun hj => absurd (Fin.ext (by simp [l]; omega)) h⟩
    have hx'' : Pi.single l (x l) ∈ Ideal.span {pb} • Submodule.span (𝓞 E) (dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb) := by
      rw [Submodule.ideal_span_singleton_smul]
      refine ⟨_, Submodule.subset_span hy, ?_⟩
      funext j
      by_cases h : j = l
      · subst h
        simp [Algebra.smul_def, mul_div_cancel₀ _ hpb0]
      · simp [h]
    refine Submodule.mem_sup.2 ⟨_, hx', _, hx'', ?_⟩
    funext j
    by_cases h : j = l
    · subst h
      simp
    · simp [h]

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 4000000 in
theorem base_step_zero_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → (H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet ((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (I.rec7 l Z).sp.gram0 (H.lev0 u).Lb) = (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
  intro B X I hI hP l Z H F A hS hH hT u pb hpb
  obtain ⟨-, -, -, hN⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  obtain ⟨hgram, hl0, -⟩ := hN 0 (Nat.zero_le _)
  have hgram0 : (I.rec7 l Z).sp.gram0 = 1 := by
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun hgram (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)) (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b)
    have e : (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a = Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b) ↔ a = b := by simp [Fin.ext_iff]
    simp only [Matrix.one_apply, e] at this
    rw [Matrix.one_apply]
    exact this
  rw [hgram0]
  obtain ⟨k, hk⟩ := (hS u).1.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb := (hH.car0 u).Lb_eq
  have hπ : (A u).piU = X.piT u := (hT.piU u).symm.trans (hS u).1.piU
  refine base_sup_dual_eq _ _ _ (X.piT u) pb ?_ (H.lev0 u).Lb_span ?_ ?_
  · have e := congrArg (fun t : 𝓞 B.host.E => (t : B.host.E)) hπ
    exact hpb.trans ((congrArg (I.rec7 l Z).host.conj e).trans (Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj (I.rec7 l Z) _).symm)
  · intro x
    have e1 : x ∈ (H.lev0 u).Lb ↔ reV (rank_eq_first_level (I.rec7 l Z).R) _ x ∈ ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb := by
      rw [hLb]
      constructor
      · exact fun h => ⟨x, h, rfl⟩
      · rintro ⟨y, hy, e⟩
        have : y = x := (reV (rank_eq_first_level (I.rec7 l Z).R) _).injective e
        exact this ▸ hy
    refine e1.trans ((hk.lb () _).trans ?_)
    constructor
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _))⟩
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _).symm)⟩
  · intro x
    have e1 : (fun j => x (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)) ∈ selfDualLatticeCoords (I.rec7 l Z) 0 (Nat.zero_le _) ↔
        x ∈ (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
      constructor
      · rintro ⟨v, hv, e⟩
        refine ⟨v, hv, ?_⟩
        funext a
        exact congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)
      · rintro ⟨v, hv, e⟩
        refine ⟨v, hv, ?_⟩
        funext j
        exact congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
    refine e1.symm.trans ((hl0 _).trans ?_)
    exact ⟨fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j), fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)⟩

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLatticeStepZeroAddConjGeneratorDualSelfDualStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLatticeStepZero_add_conjGeneratorDual_selfDual : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → (H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet ((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (I.rec7 l Z).sp.gram0 (H.lev0 u).Lb) = (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.base_step_zero_tied | exact GlobalTheory.Mem.Col2.TC.base_step_zero_tied | (intros; apply GlobalTheory.Mem.Col2.TC.base_step_zero_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnsGeneratorsBaseLatticesFunctional
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 4000000 in
theorem herm_rest_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → Formalism.L2.Herm.SymmetricCofactorCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricBaseCompatibility (I.rec7 l Z) H A ∧ Nonempty (Formalism.L2.Herm.SymmetricResidueFieldLevels (I.rec7 l Z) H A) ∧ ∃ X0 : Formalism.L2.Herm.SymmetricLevelZeroData (I.rec7 l Z) H A, ∀ u, (X0 u).piG = X.piG := by
  intro B X I hOk hP l Z H F A hS hH hT hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    have h1 := (hT.piU u).symm.trans (hS u).1.piU
    have h2 := (hT.piU (I.rec7 l Z).u₀).symm.trans (hS _).1.piU
    rw [h1, h2]
    exact hP.cof u
  · intro u pb hpb
    exact ⟨GlobalTheory.T.baseLatticeStepZero_add_conjGeneratorDual_selfDual I hOk hP l Z H F A hS hH hT u pb hpb, GlobalTheory.T.chart_base_lattice_sup_dual_selfDual I hOk hP l Z H F A hS hH hT u pb hpb⟩
  · refine ⟨fun u i h1 hm v β => ?_⟩
    by_cases h2 : i + 1 ≤ (I.rec7 l Z).R.m
    · exact (GlobalTheory.T.chartLevelFunctionals_intermediateSteps_trueColumns I hOk hP l Z H F A hS hH hT u i h1 h2 v β).some
    · have he : i = (I.rec7 l Z).R.m := by omega
      subst he
      exact (GlobalTheory.T.levelFunctional_chart_lastStep_classes I hOk hP l Z H F A hS hH hT u h1 v β).some
  · choose x hx using GlobalTheory.T.stepZeroLevel_typePrimeOrientation_frames_functionals I hOk hP l Z H F A hS hH hT hπ
    exact ⟨x, hx⟩

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnsGeneratorsBaseLatticesFunctionalStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianColumns_generators_baseLattices_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → Formalism.L2.Herm.SymmetricCofactorCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricBaseCompatibility (I.rec7 l Z) H A ∧ Nonempty (Formalism.L2.Herm.SymmetricResidueFieldLevels (I.rec7 l Z) H A) ∧ ∃ X0 : Formalism.L2.Herm.SymmetricLevelZeroData (I.rec7 l Z) H A, ∀ u, (X0 u).piG = X.piG := by
  first | exact @GlobalTheory.Mem.Col2.TC.herm_rest_tied | exact GlobalTheory.Mem.Col2.TC.herm_rest_tied | (intros; apply GlobalTheory.Mem.Col2.TC.herm_rest_tied <;> assumption)
end
