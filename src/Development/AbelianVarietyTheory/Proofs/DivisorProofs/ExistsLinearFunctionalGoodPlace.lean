module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoWEqZero
open NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinWAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def coW (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Fin a) (Fin (a + a')) (Fv F v) :=
  -(G.V.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ)

theorem coW_eq_zero (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (u : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (h : u.map (piW (t.comp σ)) = 0) : coW G t u = 0 := by
  unfold coW; rw [h]; simp

end GlobalTheory.LinWAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnipotentEmbeddingsExist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnipotentEmbeddingsExist
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LinWCoords

theorem exists_split_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (AE F E),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW (t.comp σ)) = 0 ∧ (uT Y).map (piW t) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW t) = 0 ∧ GlobalTheory.LinWAt.coW G t (uM z) = z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinWAt.coW G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinWAt.coW G t x i j * (u.map (piW t)) i j) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v t
  have hcm := hTr.base.cm
  have hP : IsUnit (G.V.J.map t).det :=
    GlobalTheory.LinBarCoords.det_map_isUnit B G.V.J 1 _ _ one_ne_zero (fun w => by rw [one_smul]; exact hTr.geo.hV.sig w) v t
  have hQ : IsUnit ((G.W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact GlobalTheory.LinBarCoords.det_map_isUnit B G.W.J Complex.I _ _ Complex.I_ne_zero hTr.geo.hW.sig v t
  set P := G.V.J.map t with hPdef
  set Q := (G.W.J.map t)ᵀ with hQdef
  let L := GlobalTheory.LinBarCoords.liftM σ hcm (m := Fin a) (n := Fin (a + a')) v t
  let uT : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun Y => L (Y, 0)) (fun Y Y' => by rw [← map_add (f := _), Prod.mk_add_mk, add_zero])
  let uM : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun z => L (0, -(P⁻¹ * z * Q⁻¹))) (fun z z' => by
      rw [Matrix.mul_add, Matrix.add_mul, neg_add, ← map_add (f := _), Prod.mk_add_mk, add_zero])
  have hco : ∀ u, GlobalTheory.LinWAt.coW G t u = -(P * u.map (piW (t.comp σ)) * Q) := fun u => by
    simp [GlobalTheory.LinWAt.coW, hPdef, hQdef]
  have hTc : ∀ Y, (uT Y).map (piW (t.comp σ)) = 0 := fun Y => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hTt : ∀ Y, (uT Y).map (piW t) = Y := fun Y => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hMc : ∀ z, (uM z).map (piW (t.comp σ)) = -(P⁻¹ * z * Q⁻¹) := fun z => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hMt : ∀ z, (uM z).map (piW t) = 0 := fun z => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hTa : ∀ Y, At (evFin F v) (uT Y) := fun Y => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  have hMa : ∀ z, At (evFin F v) (uM z) := fun z => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  refine ⟨uT, uM, fun Y => ⟨hTa Y, hTc Y, hTt Y⟩, fun z => ⟨hMa z, hMt z, ?_⟩, fun u hu => ?_, fun x u hx hu => ?_⟩
  · have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
    have e2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
    rw [hco, hMc, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
  · refine ⟨u.map (piW t), GlobalTheory.LinWAt.coW G t u, ?_⟩
    have hd : At (evFin F v) (u - (uT (u.map (piW t)) + uM (GlobalTheory.LinWAt.coW G t u))) := by
      intro c hc
      rw [smul_sub, smul_add, hu c hc, hTa _ c hc, hMa _ c hc, add_zero, sub_zero]
    refine (sub_eq_zero.1 (GlobalTheory.LinBarCoords.eq_zero_of_at σ hcm v t hd ?_ ?_))
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTt, hMt, add_zero, sub_self]
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTc, hMc, zero_add, hco, Matrix.mul_neg, Matrix.neg_mul,
        neg_neg, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, sub_self]
  · have h := GlobalTheory.T.local_lattice_hermitian_skew hcm v t G.V.J G.W.J hTr.geo.hV.herm hTr.geo.hW.skew x u hx
    dsimp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM] at h
    rw [hco, hco]
    exact h

end GlobalTheory.LinWCoords
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnipotentEmbeddingsExistStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unipotent_embeddings_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW (t.comp σ)) = 0 ∧ (uT Y).map (piW t) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW t) = 0 ∧ GlobalTheory.LinWAt.coW G t (uM z) = z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinWAt.coW G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinWAt.coW G t x i j * (u.map (piW t)) i j) := by
  first | exact @GlobalTheory.LinWCoords.exists_split_coords | exact GlobalTheory.LinWCoords.exists_split_coords | (intros; apply GlobalTheory.LinWCoords.exists_split_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinWAt

theorem nonempty_emb_of_splitsFully {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (hv : SplitsFully E v) :
    Nonempty (E →ₐ[F] Fv F v) := by
  set q : Ideal ℤ := v.asIdeal.under ℤ with hq
  obtain ⟨g, hg⟩ := (Submodule.IsPrincipal.principal q)
  have hqs : q = Ideal.span {((g.natAbs : ℕ) : ℤ)} := by
    rw [hg]; exact Eq.symm (Int.span_natAbs g)
  have hqne : q ≠ ⊥ := by
    intro h0
    apply v.ne_bot
    exact Ideal.eq_bot_of_comap_eq_bot h0
  have hg0 : g ≠ 0 := by rintro rfl; apply hqne; rw [hg]; simp
  have hp : (g.natAbs).Prime := by
    have hI : (Ideal.span {((g.natAbs : ℕ) : ℤ)}).IsPrime := hqs ▸ (Ideal.IsPrime.under ℤ v.asIdeal)
    have hne : ((g.natAbs : ℕ) : ℤ) ≠ 0 := by simpa using hg0
    exact Nat.prime_iff_prime_int.2 ((Ideal.span_singleton_prime hne).1 hI)
  have hmem : ((g.natAbs : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    have : ((g.natAbs : ℕ) : ℤ) ∈ q := by rw [hqs]; exact Ideal.subset_span rfl
    rw [hq, Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have h : (Ideal.primesOver (Ideal.span {((g.natAbs : ℕ) : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
    rw [← hqs]; exact hv
  rw [GlobalTheory.AdelicU.nonempty_split_iff hcm]
  exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two hcm.2.2.1 hp h v hmem

end GlobalTheory.LinWAt

namespace GlobalTheory.LinWAt

theorem locCo_form {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x u : W) :
    (GlobalTheory.LatVac.locCo co v x).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v x).2 = evFin F v (B x u) := by
  rw [co.form]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

theorem locCo_surj {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = w := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩
  · intro a ha
    rw [← LinearEquiv.map_smul, ← co.e.symm.map_zero]
    congr 1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

theorem at_symp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E)) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) (symp (R := AF F) (cA σ) (-1) JA JB x u) := by
  intro a ha
  have h := GlobalTheory.LatVac.symp_smul_smul σ JA JB (-1) a 1 x u
  rw [hx a ha, one_smul, mul_one, GlobalTheory.VacIndic.symp_zero_left] at h
  rw [smul_eq_mul]
  exact h.symm

theorem co_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u.map (piW t) * ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u.map (piW t) := by
  simp

theorem exists_isLinW : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v hv
  obtain ⟨t⟩ := nonempty_emb_of_splitsFully hTr.base.cm v hv.2
  obtain ⟨uT, uM, hT, hM, hspan, hsymp⟩ := (GlobalTheory.T.local_unipotent_embeddings_exist) F E σ B a a' G X om om' hTr v t
  change ∀ (x u : Matrix (Fin a) (Fin (a + a')) (AE F E)),
    At (evFin F v) x → At (evFin F v) u →
    evFin F v (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (incM F G.V.J) (incM F G.W.J) x u) =
      ∑ i, ∑ j, x.map (piW t) i j * coW G t u i j -
        ∑ i, ∑ j, coW G t x i j * u.map (piW t) i j at hsymp
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 v
  have hunr : PsiUnr B.ψ v := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hTr.base.std v
    (GlobalTheory.SplitFullyUnr.not_le_differentIdeal v hv.2)
  have hunr' : ∀ x : Fv F v, (∀ y ∈ 𝒪[Fv F v], GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
      x ∈ 𝒪[Fv F v] := by
    intro x
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    exact hunr x
  have hcoT : ∀ Y, coW G t (uT Y) = 0 := fun Y => coW_eq_zero G t _ (hT Y).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians (GlobalTheory.LatVac.psiAt B.ψ v) hψc hunr'
    ((GlobalTheory.LatVac.locCo G.M.co v).comp uT) ((GlobalTheory.LatVac.locCo G.M.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form]
      rw [hsymp _ _ (hT Y).1 (hT Y').1, hcoT, hcoT]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form]
      rw [hsymp _ _ (hM z).1 (hM z').1, (hM z).2.1, (hM z').2.1]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form]
      rw [hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.2, (hM z).2.2, hcoT, (hM z).2.1]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj G.M.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add (f := _)]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin a) (Fin (a + a')) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (G.M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v u hu φ r hr)
  refine ⟨t, ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, zero_add] at h
      rw [← (hM z).2.2]
      exact coW_eq_zero G t _ h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    rw [co_one, (hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    rw [co_one, e1, GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp _ _ _ x (uM z) hx)]
    rw [hsymp x (uM z) hx (hM z).1,
      coW_eq_zero G t x hx0, (hM z).2.1, (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (x.map (piW t))
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp

end GlobalTheory.LinWAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlaceStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_functional_good_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι := by
  first | exact @GlobalTheory.LinWAt.exists_isLinW | exact GlobalTheory.LinWAt.exists_isLinW | (intros; apply GlobalTheory.LinWAt.exists_isLinW <;> assumption)
end
