module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualAtScaled
noncomputable section

namespace GlobalTheory.AdelicU.Model

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)








section Supp

omit [NumberField E] in
theorem map_map_tens {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R'']
    [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (y : R ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) y := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

omit [NumberField E] in
theorem adTens_eq_one {y : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w y = 1) (h2 : ∀ v, compFin F E v y = 1) : y = 1 := by
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1) (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.AutFunCompare.infTens_ext fun w => (map_map_tens _ _ y).trans ((h1 w).trans (map_one _).symm))
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v =>
        (map_map_tens _ _ y).trans ((h2 v).trans (map_one _).symm))
  exact congrFun (congrFun this 0) 0

theorem idem_supp_iff {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F)
    (e0 : ∀ w, evInf F w ε = 0) (e1 : evFin F v ε = 1) (e2 : ∀ u, u ≠ v → evFin F u ε = 0) (g : GAd σ J) :
    (∀ i j, algebraMap (AF F) (AF F ⊗[F] E) ε * ((matHom _ σ J g).1 - 1) i j = ((matHom _ σ J g).1 - 1) i j) ↔
      g ∈ (emb σ J v).range := by
  have c0 : ∀ w, compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun w => by
    change evInf F w ε ⊗ₜ[F] (1 : E) = 0
    rw [e0, TensorProduct.zero_tmul]
  have c1 : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) ε) = 1 := by
    change evFin F v ε ⊗ₜ[F] (1 : E) = 1
    rw [e1]; rfl
  have c2 : ∀ u, u ≠ v → compFin F E u (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun u hu => by
    change evFin F u ε ⊗ₜ[F] (1 : E) = 0
    rw [e2 u hu, TensorProduct.zero_tmul]
  have one : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : Matrix (Fin n) (Fin n) A),
      m.map φ = 1 ↔ ∀ i j, φ ((m - 1) i j) = 0 := fun φ m => by
    rw [← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have pf : ∀ u, proj σ J u g = 1 ↔ ∀ i j, compFin F E u (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  have pa : ∀ w, projArch σ J w g = 1 ↔ ∀ i j, compInf F E w (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  rw [range_emb, mem_atPts, mem_finPts_iff_forall]
  simp only [pf, pa, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨fun w i j => by rw [← h, map_mul, c0, zero_mul], fun u hu i j => by rw [← h, map_mul, c2 u hu, zero_mul]⟩
  · rintro ⟨h1, h2⟩ i j
    rw [← sub_eq_zero, ← add_eq_right (b := 1)]
    refine adTens_eq_one (fun w => ?_) fun u => ?_
    · rw [map_add (f := _), map_sub, map_mul, h1, map_one]; simp
    · rw [map_add (f := _), map_sub, map_mul, map_one]
      by_cases hu : u = v
      · subst hu; rw [c1]; simp
      · rw [h2 u hu]; simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem suppF_iff {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (h : IsPlaceIdem D v ε) (g : GA D V) :
    Formalism.IndefR.Mult.SuppF V (algebraMap (AF D.host.F) (AE D) ε) g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  exact idem_supp_iff _ _ v _ (fun _ => rfl) h1 h2 g

theorem emb_mem_KsphC_iff {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : GLoc D.sp.cm.sig V.gram v) :
    emb D.sp.cm.sig V.gram v x ∈ KsphC V ∅ ↔ x ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v := by
  rw [KsphC_eq]
  exact ⟨fun h => by simpa using (mem_levelOff.1 h).2.2 v (by simp), emb_mem_levelOff (by simp)⟩

end Supp

section More

end More

end GlobalTheory.AdelicU.Model
end
end

noncomputable section

namespace GlobalTheory.LevelClosure

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter Topology

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open Classical in
def cutIdem (T : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun v => if v ∈ T then 1 else 0, Eventually.of_forall fun v => by
    by_cases h : v ∈ T
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem evalV_cutIdem_of_mem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 1 := by
  classical
  exact if_pos h

theorem evalV_cutIdem_of_notMem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 0 := by
  classical
  exact if_neg h

theorem tendsto_cutIdem_mul (a : Af F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutIdem T * a) atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ principal S := by
    rw [le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T =>
    ⟨fun v => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v, by
      rw [eventually_principal]
      intro w hw
      by_cases h : w ∈ T
      · simp only [evalV_cutIdem_of_mem h, one_mul]; exact hw
      · simp only [evalV_cutIdem_of_notMem h, zero_mul]; exact zero_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [eventually_principal]; exact fun w hw => hw⟩
  have hf : Tendsto f atTop (𝓝 a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v
    rw [evalV_cutIdem_of_mem this, one_mul]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem tendsto_cutIdem_smul (z : Af F ⊗[F] E) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => (cutIdem T : Af F) • z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  induction z using TensorProduct.induction_on with
  | zero => simpa using tendsto_const_nhds
  | add x y hx hy => simpa only [smul_add] using hx.add hy
  | tmul a x =>
    have h := (tendsto_cutIdem_mul a).smul_const ((1 : Af F) ⊗ₜ[F] x)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def cutPt (T : Finset (HeightOneSpectrum (𝓞 F))) : GAd σ J →* GAd σ J := (embAt σ J T).comp (projAt σ J T)

omit [NumberField E] in
theorem map_smul_cut (v : HeightOneSpectrum (𝓞 F)) (c : Af F) (z : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (c • z) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c • Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul a x => simp [TensorProduct.smul_tmul']

omit [NumberField E] in
theorem cutPt_entry (T : Finset (HeightOneSpectrum (𝓞 F))) (g : GAd σ J) (i j : Fin n) :
    (matHom _ σ J (projFin σ J (cutPt σ J T g))).1 i j =
      (cutIdem T : Af F) • ((matHom _ σ J (projFin σ J g)).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) +
        (1 : Matrix (Fin n) (Fin n) _) i j := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => ?_
  have e : ∀ g : GAd σ J, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((matHom _ σ J (projFin σ J g)).1 i j) = (matHom _ σ J (proj σ J v g)).1 i j := fun g => by
    rw [← projFinLoc_projFin]; rfl
  have e1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _ =
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _
  rw [map_add (f := _), map_smul_cut, map_sub, e, e, e1]
  by_cases hv : v ∈ T
  · have : proj σ J v (cutPt σ J T g) = proj σ J v g := proj_embAt σ J T _ ⟨v, hv⟩
    rw [this, evalV_cutIdem_of_mem hv, one_smul, sub_add_cancel]
  · have : proj σ J v (cutPt σ J T g) = 1 := (mem_atPts.1 (embAt_mem σ J T _)).2 v hv
    rw [this, evalV_cutIdem_of_notMem hv, zero_smul, zero_add, map_one, Units.val_one]

theorem tendsto_projFin_cutPt (g : GAd σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => projFin σ J (cutPt σ J T g)) atTop (𝓝 (projFin σ J g)) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  have h : ∀ g : GAd σ J, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (matHom _ σ J (projFin σ J (cutPt σ J T g))).1) atTop (𝓝 (matHom _ σ J (projFin σ J g)).1) := fun g => by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [cutPt_entry]
    have := (tendsto_cutIdem_smul ((matHom _ σ J (projFin σ J g)).1 i j -
      (1 : Matrix (Fin n) (Fin n) _) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
    rwa [sub_add_cancel] at this
  rw [(isEmbedding_matHom _ σ J).tendsto_nhds_iff, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h g).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h g⁻¹
  simp only [map_inv] at h2
  exact h2

theorem tendsto_cutPt {g : GAd σ J} (hg : g ∈ finPts σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutPt σ J T g) atTop (𝓝 g) := by
  have e : ∀ g ∈ finPts σ J, ofFin σ J (projFin σ J g) = g := fun g hg =>
    ext_inf_fin σ J (by simp [mem_finPts.1 hg]) (by simp)
  have h := ((continuous_ofFin σ J).tendsto _).comp (tendsto_projFin_cutPt σ J g)
  rw [e g hg] at h
  exact h.congr fun T => e _ (mem_atPts.1 (embAt_mem σ J T _)).1

theorem mem_of_isClosed {H : Subgroup (GAd σ J)} (hH : IsClosed (H : Set (GAd σ J))) {g : GAd σ J}
    (hg : g ∈ finPts σ J) (h : ∀ v, emb σ J v (proj σ J v g) ∈ H) : g ∈ H :=
  hH.mem_of_tendsto (tendsto_cutPt σ J hg) (Eventually.of_forall fun T =>
    Subgroup.noncommProd_mem H (f := fun v : T => emb σ J v (proj σ J v g))
      (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => h v)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ksph_le_of_isClosed : ∀ (D : D7) (V : HSp D) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (H : Subgroup (GA D V)), IsClosed (H : Set (GA D V)) → (∀ v, v ∉ Z → ∀ ε, IsPlaceIdem D v ε → ∀ g ∈ KsphC V ∅, SuppPl ε V g → g ∈ H) → ∀ k ∈ KsphC V Z, k ∈ H := by
  intro D V Z H hH h k hk
  rw [KsphC_eq] at hk
  obtain ⟨h1, h2, h3⟩ := mem_levelOff.1 hk
  refine mem_of_isClosed D.sp.cm.sig V.gram hH h1 fun v => ?_
  by_cases hv : v ∈ Z
  · rw [h2 v hv, map_one]; exact one_mem _
  · have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleFin v 1)) :=
      ⟨_, rfl, evalV_singleFin_self v 1, fun _ hu => evalV_singleFin_ne hu 1⟩
    exact h v hv _ hε _ ((Model.emb_mem_KsphC_iff V v _).2 (h3 v hv)) ((Model.suppF_iff V hε _).2 ⟨_, rfl⟩)

end GlobalTheory.LevelClosure

end
