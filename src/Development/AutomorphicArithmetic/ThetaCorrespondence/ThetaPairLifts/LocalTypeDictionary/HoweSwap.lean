module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.HoweDualityUnramifiedAllPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalHoweTransferRealPlace
section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.HoweGlobal.RealTransfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealActs
theorem howe_real_place_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    Module.rank ℂ ↥(G.M.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobal.relInf Bs G om ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobal.relInf Bs G om ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ →
        N ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobal.relInf Bs G om ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype),
      g x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hM.triple
  have PA : PolActs Bs G.M om := _root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs _ _ _ _ G.M _ _ om _ _ _ _ hPair
  set P := G.M.Pol Bs.ψ Bs.emb with hPdef
  have key : ∀ N : Submodule ℂ ↥P, relInf Bs G om ≤ N → (∀ g ∈ opInf Bs G om, ∀ x ∈ N, g x ∈ N) →
      GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N.map P.subtype) := by
    intro N hrel hop
    refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨D, hDP, hD⟩ := PA.1 γ hγ
      have e : f₁ = D f := (hD f hf f₁).1 hA
      have h1 : f₁ ∈ P := e ▸ hDP f hf
      refine ⟨⟨f₁, h1⟩, hrel (Submodule.subset_span (Or.inl ⟨γ, hγ, f, hf, hA⟩)), rfl⟩
    · intro k hk f hf f₁ hA
      obtain ⟨D, hDP, hD⟩ := PA.2.1 k hk
      have e : f₁ = D f := (hD f hf f₁).1 hA
      have h1 : f₁ ∈ P := e ▸ hDP f hf
      refine ⟨⟨f₁, h1⟩ - ⟨f, hf⟩, hrel (Submodule.subset_span (Or.inr ⟨k, hk, ⟨f, hf⟩, ⟨f₁, h1⟩, hA, rfl⟩)), rfl⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hDP, hD⟩ := PA.2.2.1 γ hγ
      let g : Module.End ℂ ↥P := D.restrict hDP
      have hg : g ∈ opInf Bs G om := Or.inr ⟨γ, hγ, fun f => (hD f f.2 _).2 rfl⟩
      have e : f₁ = D y := (hD y y.2 f₁).1 hA
      exact ⟨g y, hop g hg y hy, e.symm⟩
    · intro k hk f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hDP, hD⟩ := PA.2.2.2 k hk
      let g : Module.End ℂ ↥P := D.restrict hDP
      have hg : g ∈ opInf Bs G om := Or.inl ⟨k, hk, fun f => (hD f f.2 _).2 rfl⟩
      have e : f₁ = D y := (hD y y.2 f₁).1 hA
      exact ⟨g y, hop g hg y hy, e.symm⟩
  have hinj : Function.Injective (Submodule.map P.subtype) :=
    Submodule.map_injective_of_injective P.injective_subtype
  have hne : ∀ N : Submodule ℂ ↥P, N ≠ ⊤ → N.map P.subtype ≠ P := by
    intro N hN h
    apply hN
    apply hinj
    rw [h, Submodule.map_subtype_top]
  refine ⟨_root_.GlobalTheory.T.polarization_rank_le_dim hP F E σ Bs _ _ _ _ G.M _ _ om _ _ _ _ hPair, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hreal.1
    refine ⟨L, fun m N hN hN' => hL m (fun i => (N i).map P.subtype)
      ((Submodule.map_strictMono_of_injective P.injective_subtype).comp hN) fun i => key _ (hN' i).1 (hN' i).2⟩
  · intro N hrel hop hN x hx
    exact hreal.2 _ (key N hrel hop) (hne N hN) x ⟨x, hx, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro x (⟨γ, hγ, f, hf, hA⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
    · exact hM.real.quot.lie γ hγ f hf _ hA
    · show R.p (((f₁ - f : ↥P)) : SInf F _) = 0
      rw [Submodule.coe_sub, map_sub, hM.real.quot.cpt k hk f f.2 f₁ hA, sub_self]
  · intro g hg x hx
    have hx' : R.p (x : SInf F _) = 0 := hx
    show R.p ((g x : ↥P) : SInf F _) = 0
    rcases hg with ⟨k, hk, hA⟩ | ⟨γ, hγ, hA⟩
    · have := hM.real.cpt k hk x x.2 0 (G.M'.Pol Bs.ψ Bs.emb).zero_mem _ 0 (hA x)
        (GlobalTheory.ThK.RealUniq.acts_zero _) (by rw [hx', map_zero])
      rw [this, map_zero]
    · have := hM.real.lie γ hγ x x.2 0 (G.M'.Pol Bs.ψ Bs.emb).zero_mem _ 0 (hA x)
        (GlobalTheory.ThK.RealUniq.actsD_zero _) (by rw [hx', map_zero])
      rw [this, map_zero]
end GlobalTheory.HoweGlobal.RealTransfer
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_howe_transfer_real_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    Module.rank ℂ ↥(G.M.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobal.relInf Bs G om ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobal.relInf Bs G om ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ →
        N ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobal.relInf Bs G om ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype),
      g x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) := by
  first | exact @_root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer | exact _root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer | (intros; apply _root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalHoweTensorProductTransfer
section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open scoped Classical
namespace GlobalTheory.HoweGlobal.Transfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}
variable (M : Model σ Y W) (T : Finset (Pl F))
end GlobalTheory.HoweGlobal.Transfer
end
noncomputable section
open scoped Classical
namespace GlobalTheory.HoweGlobal.Transfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (T : Finset (Pl F))
end GlobalTheory.HoweGlobal.Transfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweGlobal.Transfer in
theorem GlobalTheory.HoweGlobal.howe_tensor_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) [DecidableEq {v // v ∈ T}]
      (L : ↥(G.M.Pol Bs.ψ Bs.emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ] ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(G.M.Pol Bs.ψ Bs.emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = G.M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobal.relInf Bs G om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ v : T, ∀ x ∈ GlobalTheory.HoweGlobal.relFin G om v.1, ∀ (x₀ : ↥(G.M.Pol Bs.ψ Bs.emb))
          (y : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y v x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ v : T, ∀ g ∈ GlobalTheory.HoweGlobal.opFin G om v.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)) →ₗ[ℂ] _)) v g)) t) ∈ N) := by
  intro _ F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hm N hN T _ L hL
  have hM := hm.triple.geo.hM
  have hLe : ∀ (f : ↥(G.M.Pol Bs.ψ Bs.emb)) (φ : ∀ v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1))),
      L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = pure (f : SInf F (Fin a × Fin (a + a'))) (ext G.M T φ) :=
    fun f φ => hL f φ _ (fun v h => ext_of_mem G.M T φ ⟨v, h⟩) (fun v h => ext_of_not_mem G.M T φ v h)
  have hpA := pure_mem_algD G.M T Bs.emb hM
  have hR := rest_ext G.M T hM
  have hLA : ∀ t, L t ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb := by
    intro t
    refine mem_of_pure ((GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb).comap L) (fun x φ => ?_) t
    rw [Submodule.mem_comap, hLe]
    exact hpA _ x.2 φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have key : ∀ φ : ∀ v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1)),
        GlobalTheory.HoweGlobal.relInf Bs G om ≤ N.comap (L ∘ₗ (TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ φ)) := by
      intro φ
      refine Submodule.span_le.2 ?_
      rintro x (⟨γ, hγ, f, hf, hD⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
      · show L (x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        rw [hLe]
        exact hN.2.2.2 γ hγ _ (hpA f hf φ) _ (hpA _ x.2 φ) (fun z => hD _ (hR f φ) z)
      · show L ((f₁ - f) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        have e : pure ((f₁ : SInf F (Fin a × Fin (a + a')))) (ext G.M T φ) =
            om (k, 1) (pure (f : SInf F (Fin a × Fin (a + a'))) (ext G.M T φ)) := (hA _ (hR _ φ)).symm
        rw [TensorProduct.sub_tmul, map_sub, hLe, hLe, e]
        exact hN.2.2.1 k hk _ (hpA _ f.2 φ)
    intro x hx y
    exact mem_of_tprod (N.comap (L ∘ₗ TensorProduct.mk ℂ _ _ x)) (fun φ => key φ hx) y
  · intro v x hx x₀ y
    let ℓ := L ∘ₗ TensorProduct.mk ℂ _ _ x₀ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y v
    have hℓ : ∀ z, ℓ z = L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y v z)) := fun z => rfl
    have hsub : augAt om v.1 ≤ (N.comap ℓ).map (SB (Fin a × Fin (a + a') → Fv F v.1)).subtype := by
      refine Submodule.span_le.2 ?_
      rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
      refine ⟨⟨φ₁, hφ₁⟩ - ⟨φ, hφ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, hℓ, hℓ, hLe, hLe]
      have e : om (g, 1) (pure (x₀ : SInf F (Fin a × Fin (a + a'))) (ext G.M T (Function.update y v ⟨φ, hφ⟩))) =
          pure (x₀ : SInf F (Fin a × Fin (a + a'))) (ext G.M T (Function.update y v ⟨φ₁, hφ₁⟩)) := by
        rw [acts_ext G.M T hM (x₀ : SInf F (Fin a × Fin (a + a'))) (Function.update y v ⟨φ, hφ⟩) v ⟨φ₁, hφ₁⟩ ⇑(om (g, 1))
          (by rw [Function.update_self]; exact hA), Function.update_idem]
      rw [← e]
      exact hN.2.1 v.1 g hg _ (hpA _ x₀.2 _)
    obtain ⟨x', hx', he⟩ := hsub (Submodule.mem_comap.1 hx)
    have : x' = x := Subtype.ext he
    rw [← hℓ, ← this]
    exact hx'
  · intro g hg t ht
    rcases hg with ⟨k, hk, hkA⟩ | ⟨γ, hγ, hgD⟩
    · have e : ∀ t, L (TensorProduct.map g LinearMap.id t) = om (1, k) (L t) := by
        intro t
        refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map g LinearMap.id)
          ((om (1, k)) ∘ₗ L)) (fun x φ => ?_) t)
        refine LinearMap.mem_eqLocus.2 ?_
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact (hkA x _ (hR _ φ)).symm
      rw [e]
      exact hN.1.2.2.1 k hk _ ht
    · let S : Submodule ℂ (↥(G.M.Pol Bs.ψ Bs.emb) ⊗[ℂ]
          (⨂[ℂ] v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1)))) :=
        { carrier := {t | ∀ z, HasDerivAt (fun s : ℝ => om (1, γ (Multiplicative.ofAdd s)) (L t) z)
            (L (TensorProduct.map g LinearMap.id t) z) 0}
          add_mem' := fun {t₁ t₂} h₁ h₂ z => by
            simp only [map_add (f := _), Pi.add_apply]
            exact (h₁ z).add (h₂ z)
          zero_mem' := fun z => by
            simp only [map_zero, Pi.zero_apply]
            exact hasDerivAt_const 0 0
          smul_mem' := fun c t h z => by
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
            exact (h z).const_mul c }
      have hS : ∀ t, t ∈ S := mem_of_pure S (fun x φ z => by
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact hgD x _ (hR _ φ) z)
      exact hN.1.2.2.2 γ hγ _ ht _ (hLA _) (hS t)
  · intro v g hg t ht
    obtain ⟨h, hh, hA⟩ := hg
    have e : ∀ t, L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
        (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g)) t) = om (1, h) (L t) := by
      intro t
      refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update
          (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g)))
          ((om (1, h)) ∘ₗ L)) (fun x φ => ?_) t)
      refine LinearMap.mem_eqLocus.2 ?_
      have hφ : (fun w => (Function.update
          (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g w) (φ w)) =
          Function.update φ v (g (φ v)) := by
        funext w
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod, hLe]
      rw [hφ, acts_ext G.M T hM _ φ v (g (φ v)) _ (hA (φ v))]
    rw [e]
    exact hN.1.2.1 v.1 h hh _ ht
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_howe_tensor_product_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) [DecidableEq {v // v ∈ T}]
      (L : ↥(G.M.Pol Bs.ψ Bs.emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ] ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(G.M.Pol Bs.ψ Bs.emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = G.M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobal.relInf Bs G om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ v : T, ∀ x ∈ GlobalTheory.HoweGlobal.relFin G om v.1, ∀ (x₀ : ↥(G.M.Pol Bs.ψ Bs.emb))
          (y : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y v x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ v : T, ∀ g ∈ GlobalTheory.HoweGlobal.opFin G om v.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)) →ₗ[ℂ] _)) v g)) t) ∈ N) := by
  first | exact @_root_.GlobalTheory.HoweGlobal.howe_tensor_transfer | exact _root_.GlobalTheory.HoweGlobal.howe_tensor_transfer | (intros; apply _root_.GlobalTheory.HoweGlobal.howe_tensor_transfer <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaJetCondition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.TwistedThetaJetCondition : Prop :=  GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N →
      N ≠ algD Γ.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaKernelCondition
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.TwistedThetaKernelCondition : Prop :=  GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix
noncomputable section
namespace UpperTheory.Lit.HoweDuality
open GlobalTheory.HoweGlobalPair
theorem stageV_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), Xc.T ⊆ T →
        GlobalTheory.HoweGlobal.algAt G.M Bs.ψ Bs.emb T ≤ N ∨
          ∀ Φ ∈ N, Φ ∈ GlobalTheory.HoweGlobal.algAt G.M Bs.ψ Bs.emb T → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0 := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN T hT
  classical
  obtain ⟨L, hL, hrange⟩ := GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors G.M Bs.ψ Bs.emb hM.triple.geo.hM.std T
  have hloc := _root_.GlobalTheory.T.global_howe_transfer_real_place hP F E σ Bs a a' G Xc om om' R Rf hM hreal
  have hfl := fun v => locV hM v
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.T.global_howe_tensor_product_transfer hP F E σ Bs a a' G Xc om om' R Rf hM N hN T L hL
  have key := tens (ι := T) (M₀ := ↥(G.M.Pol Bs.ψ Bs.emb))
    (M := fun v : T => ↥(SB (Fin a × Fin (a + a') → Fv F v.1)))
    (GlobalTheory.HoweGlobal.opInf Bs G om) (fun v => GlobalTheory.HoweGlobal.opFin G om v.1)
    (GlobalTheory.HoweGlobal.relInf Bs G om) (fun v => GlobalTheory.HoweGlobal.relFin G om v.1)
    (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) (fun v => Rf.p v.1 ∘ₗ (SB _).subtype)
    hloc.1 (fun v => GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le F _ v.1) hloc.2.1 hloc.2.2.1 hloc.2.2.2.1 hloc.2.2.2.2
    (fun v => (hfl v.1).1) (fun v => (kerV hM v.1).2.1) (fun v => (hfl v.1).2) (fun v => (kerV hM v.1).2.2.2)
    (N.comap L) h1 h2 h3 h4
  rcases key with htop | hker
  · left
    intro Φ hΦ
    obtain ⟨t, rfl⟩ := hrange hΦ
    have ht : t ∈ N.comap L := by rw [htop]; exact Submodule.mem_top
    exact ht
  · right
    intro Φ hΦN hΦT
    obtain ⟨t, rfl⟩ := hrange hΦT
    have ht0 := hker (show t ∈ N.comap L from hΦN)
    obtain ⟨m, f, φ, rfl⟩ := GlobalTheory.HoweGlobal.decomp t
    refine ⟨T, hT, m, 0, fun j => ((f j : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F (Fin a × Fin (a + a'))),
      fun j v => if h : v ∈ T then ((φ j ⟨v, h⟩ : ↥(SB _)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) else G.M.vac v,
      Fin.elim0, Fin.elim0, fun j => ⟨(f j).2, fun v => ?_, fun v hv => by simp only [dif_neg hv]⟩, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
    · by_cases h : v ∈ T
      · simp only [dif_pos h]; exact (φ j ⟨v, h⟩).2
      · simp only [dif_neg h]; exact (hM.triple.geo.hM.vac v).1
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => hL _ _ _ (fun v h => by simp only [dif_pos h]) (fun v h => by simp only [dif_neg h])
    · simp
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [LinearMap.mem_ker, map_sum] at ht0
        rw [Fin.sum_univ_zero, ← ht0]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
        simp
theorem allV_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0 := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN hne ΦD hΦ
  by_contra hc
  obtain ⟨T, hT, hΦT⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M Bs.ψ Bs.emb (hN.1.1 hΦ) Xc.T
  apply hne
  refine le_antisymm hN.1.1 fun Ψ hΨ => ?_
  obtain ⟨T', hT', hΨT'⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M Bs.ψ Bs.emb hΨ T
  rcases _root_.UpperTheory.Lit.HoweDuality.stageV_alt hP F E σ Bs a a' G Xc om om' R Rf hM hreal N hN T' (hT.trans hT') with h | h
  · exact h hΨT'
  · exact absurd (h ΦD hΦ (GlobalTheory.HoweGlobal.algAt_mono G.M Bs.ψ Bs.emb hT' hΦT)) hc
theorem twisted_theta_kernel_condition : _root_.GlobalTheory.T.TwistedThetaKernelCondition := fun hR hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM N hN hne =>
  _root_.UpperTheory.Lit.HoweDuality.allV_alt hP F E σ Bs a a' G Xc om om' R Rf hM (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
theorem twisted_theta_jet_condition : _root_.GlobalTheory.T.TwistedThetaJetCondition := fun hR _ F E _ _ _ _ _ σ a a' Bs G Xc om om' R Rf hM N hN hne =>
  allVp F E σ Bs a a' G Xc om om' R Rf hM (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift_smallPair hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
end UpperTheory.Lit.HoweDuality
end
end
