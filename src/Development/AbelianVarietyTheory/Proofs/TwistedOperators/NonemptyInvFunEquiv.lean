module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Formalism.LocalToGlobal.KernelLattices.ThDistC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
noncomputable section

open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct

namespace GlobalTheory.OneFunctional

section General

variable {G H K V W X : Type} [Monoid G] [Monoid H] [Monoid K] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

def Iso (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ g x, e (ρ g x) = σ g (e x)

theorem Iso.refl (ρ : Representation ℂ G V) : Iso ρ ρ := ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem Iso.symm {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) : Iso σ ρ := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun g x => e.injective (by rw [he]; simp)⟩

theorem Iso.trans {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X} (h : Iso ρ σ)
    (h' : Iso σ τ) : Iso ρ τ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun g x => by simp [he, he']⟩

theorem Iso.comp {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (f : H →* G) :
    Iso (ρ.comp f : Representation ℂ H V) (σ.comp f) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun g x => he (f g) x⟩

theorem Iso.twist {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (χ : G →* ℂˣ) :
    Iso (twist χ ρ) (twist χ σ) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun g x => ?_⟩
  change e ((χ g : ℂ) • ρ g x) = (χ g : ℂ) • σ g (e x)
  rw [map_smul, he]

theorem Iso.tprod {V' W' : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}
    (h : Iso ρ σ) (h' : Iso ρ' σ') : Iso (ρ.tprod ρ') (σ.tprod σ') := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨TensorProduct.congr e e', fun g x => ?_⟩
  induction x with
  | tmul a b => simp [he, he']
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem Iso.tprod_comm (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Iso (ρ.tprod σ) (σ.tprod ρ) := by
  refine ⟨TensorProduct.comm ℂ V W, fun g x => ?_⟩
  induction x with
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem Iso.dual {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Iso ρ.dual σ.dual := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap, fun g x => ?_⟩
  ext w
  simp [Module.Dual.transpose_apply, he]

theorem Iso.of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) : Iso ρ σ :=
  ⟨e.toLinearEquiv, fun g x => e.toIntertwiningMap.isIntertwining _ _ g x⟩

theorem mem_invFun {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} : l ∈ invFun ρ ↔ ∀ g x, l (ρ g x) = l x := Iff.rfl

theorem Iso.nonempty_invFun_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Nonempty (invFun ρ ≃ₗ[ℂ] invFun σ) := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap.ofSubmodules _ _ (le_antisymm ?_ fun l hl => ⟨e.symm.dualMap l, fun g x => ?_, ?_⟩)⟩
  · rintro _ ⟨l, hl, rfl⟩ g x
    change l (e (σ g x)) = l (e x)
    rw [he, hl]
  · obtain ⟨x, rfl⟩ := e.surjective x
    change l (e.symm _) = l (e.symm _)
    rw [← he, e.symm_apply_apply, e.symm_apply_apply, hl]
  · ext x
    simp

theorem Iso.finrank_invFun {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Module.finrank ℂ (invFun ρ) = Module.finrank ℂ (invFun σ) := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  exact e.finrank_eq

theorem Iso.invFun_eq_bot {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (h0 : invFun σ = ⊥) :
    invFun ρ = ⊥ := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  rw [← Submodule.subsingleton_iff_eq_bot] at h0 ⊢
  exact e.toEquiv.subsingleton

def Contracts {F : Type} [AddCommGroup F] [Module ℂ F] (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V)
    (σ' : Representation ℂ G W) : Prop :=
  ∃ π : F ⊗[ℂ] V →ₗ[ℂ] W, Function.Surjective π ∧
    (∀ h g f v, π (φ (h, g) f ⊗ₜ σ h v) = σ' g (π (f ⊗ₜ v))) ∧
    ∀ l : Module.Dual ℂ (F ⊗[ℂ] V), (∀ h f v, l (φ (h, 1) f ⊗ₜ σ h v) = l (f ⊗ₜ v)) → ∀ x, π x = 0 → l x = 0

theorem Contracts.congr {F F' V' W' : Type} [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {φ : Representation ℂ (H × G) F} {σ : Representation ℂ H V} {τ : Representation ℂ G W}
    {φ' : Representation ℂ (H × G) F'} {σ' : Representation ℂ H V'} {τ' : Representation ℂ G W'}
    (h : Contracts φ σ τ) (h1 : Iso φ φ') (h2 : Iso σ σ') (h3 : Iso τ τ') : Contracts φ' σ' τ' := by
  obtain ⟨π, hs, he, hk⟩ := h
  obtain ⟨e1, he1⟩ := h1
  obtain ⟨e2, he2⟩ := h2
  obtain ⟨e3, he3⟩ := h3
  refine ⟨e3.toLinearMap ∘ₗ π ∘ₗ (TensorProduct.congr e1 e2).symm.toLinearMap,
    e3.surjective.comp (hs.comp (TensorProduct.congr e1 e2).symm.surjective), fun h g f v => ?_, fun l hl x hx => ?_⟩
  · obtain ⟨f, rfl⟩ := e1.surjective f
    obtain ⟨v, rfl⟩ := e2.surjective v
    simp [← he1, ← he2, he, he3]
  · obtain ⟨x, rfl⟩ := (TensorProduct.congr e1 e2).surjective x
    refine hk (l ∘ₗ (TensorProduct.congr e1 e2).toLinearMap) (fun h f v => ?_) x ?_
    · simp [he1, he2, hl]
    · change e3 (π ((TensorProduct.congr e1 e2).symm ((TensorProduct.congr e1 e2) x))) = 0 at hx
      simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.map_eq_zero_iff] using hx

end General

section Outer

variable {ι G H : Type} [Monoid G] [Monoid H] {V W : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]

def outer (ρ : ∀ τ, Representation ℂ G (V τ)) : Representation ℂ (ι → G) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp (Pi.evalMonoidHom (fun _ : ι => G) τ)

def outer₂ (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) : Representation ℂ ((ι → H) × (ι → G)) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp ((Pi.evalMonoidHom (fun _ : ι => H) τ).prodMap (Pi.evalMonoidHom (fun _ : ι => G) τ))

theorem piTprod_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : G) :
    piTprod ρ g = PiTensorProduct.map fun τ => ρ τ g := rfl

theorem outer_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : ι → G) :
    outer ρ g = PiTensorProduct.map fun τ => ρ τ (g τ) := rfl

theorem outer₂_apply (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) (h : ι → H) (g : ι → G) :
    outer₂ ρ (h, g) = PiTensorProduct.map fun τ => ρ τ (h τ, g τ) := rfl

theorem Iso.outer {ρ : ∀ τ, Representation ℂ G (V τ)} {σ : ∀ τ, Representation ℂ G (W τ)} (h : ∀ τ, Iso (ρ τ) (σ τ)) :
    Iso (outer ρ) (outer σ) := by
  choose e he using h
  refine ⟨PiTensorProduct.congr e, fun g x => ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v => simp [outer_apply, he]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end Outer

abbrev U (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

def conjU (n : ℕ) : U n →* U n where
  toFun g := ⟨(star g.1)ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star g.1 * g.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 g.2
    have e : star (star g.1)ᵀ = (g.1)ᵀ := by ext i j; simp
    rw [e, ← Matrix.transpose_mul, mul_eq_one_comm.1 h, Matrix.transpose_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [star_mul, Matrix.transpose_mul])

@[simp] theorem conjU_coe (n : ℕ) (g : U n) : (conjU n g).1 = (star g.1)ᵀ := rfl

abbrev irr (n : ℕ) (lam : DomWeight n) : Representation ℂ (U n) (nablaSq ℂ n lam) := smallRep (unitaryIncl n) lam

def fockOne (a b : ℕ) (α β : ℤ) : Representation ℂ (U a × U b) (MvPolynomial (Fin b × Fin a) ℂ) :=
  twist ((detU a ^ α).comp (MonoidHom.fst _ _) * (detU b ^ β).comp (MonoidHom.snd _ _))
    (GlobalTheory.GLDuality.polyRep ((unitaryIncl a).comp (conjU a)) (unitaryIncl b))

def StepW {a b : ℕ} (α β : ℤ) (lam : DomWeight a) (lam' : DomWeight b) : Prop :=
  ∀ i : Fin b, lam'.w i = if h : i.1 < a then lam.w ⟨i.1, h⟩ + α + β else β

end GlobalTheory.OneFunctional
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepIdentities
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainStepIdentities

theorem volAdd_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (r : ℕ) :
    volAdd ν r = ∏ i ∈ Finset.Icc 1 r, (zetaAt (resCard k) i)⁻¹ := by
  have := hν.1
  have h := GlobalTheory.IndexVolume.volumeOfGL ν hν.2 (Fin r)
  have hS : (Units.val '' (KO k (Fin r) : Set (GL (Fin r) k)) : Set (Matrix (Fin r) (Fin r) k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.groupSet (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, trivial, rfl⟩
    · rintro ⟨g, -, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, rfl⟩
  have e : volAdd ν r = GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup ν (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    unfold volAdd GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup
    rw [hS]
    rfl
  rw [e, h, Fintype.card_fin, Formalism.MainNotions.ZetaProductPairs.qE]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [zetaAt, GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.resCard, resCard, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.ChainStepIdentities
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockVolumeProd
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockVolumeProd
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.BlockVolume

variable {k : Type} [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν]

def rowSplit (A D : Type) [Fintype A] [Fintype D] :
    ((A ⊕ D) → k) ≃ᵐ ((A → k) × (D → k)) :=
  MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => k)

theorem rowSplit_mp (A D : Type) [Fintype A] [Fintype D] :
    MeasurePreserving (rowSplit (k := k) A D) (Measure.pi fun _ : A ⊕ D => ν)
      ((Measure.pi fun _ : A => ν).prod (Measure.pi fun _ : D => ν)) :=
  measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => ν)

def colSplit (R A D : Type) [Fintype R] [Fintype A] [Fintype D] :
    (R → (A ⊕ D) → k) ≃ᵐ ((R → A → k) × (R → D → k)) :=
  (MeasurableEquiv.piCongrRight fun _ : R => rowSplit (k := k) A D).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (A → k) (D → k) R)

theorem colSplit_mp (R A D : Type) [Fintype R] [Fintype A] [Fintype D] :
    MeasurePreserving (colSplit (k := k) R A D)
      (Measure.pi fun _ : R => Measure.pi fun _ : A ⊕ D => ν)
      ((Measure.pi fun _ : R => Measure.pi fun _ : A => ν).prod
        (Measure.pi fun _ : R => Measure.pi fun _ : D => ν)) := by
  have h1 := measurePreserving_pi (fun _ : R => Measure.pi fun _ : A ⊕ D => ν)
    (fun _ : R => (Measure.pi fun _ : A => ν).prod (Measure.pi fun _ : D => ν))
    (fun _ => rowSplit_mp ν A D)
  have h2 := measurePreserving_arrowProdEquivProdArrow (A → k) (D → k) R
    (fun _ => Measure.pi fun _ : A => ν) (fun _ => Measure.pi fun _ : D => ν)
  exact h2.comp h1

def blockSplit (A D : Type) [Fintype A] [Fintype D] :
    ((A ⊕ D) → (A ⊕ D) → k) ≃ᵐ (((A → A → k) × (A → D → k)) × ((D → A → k) × (D → D → k))) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => (A ⊕ D) → k)).trans
    (MeasurableEquiv.prodCongr (colSplit A A D) (colSplit D A D))

def blockEquiv (A D : Type) [Fintype A] [Fintype D] :
    Matrix (A ⊕ D) (A ⊕ D) k ≃ᵐ ((Matrix A A k × Matrix A D k) × (Matrix D A k × Matrix D D k)) :=
  blockSplit (k := k) A D

theorem blockSplit_mp (A D : Type) [Fintype A] [Fintype D] :
    MeasurePreserving (blockEquiv (k := k) A D) (volM ν (A ⊕ D) (A ⊕ D))
      (((volM ν A A).prod (volM ν A D)).prod ((volM ν D A).prod (volM ν D D))) := by
  have h1 := measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => Measure.pi fun _ : A ⊕ D => ν)
  have h2 := (colSplit_mp ν A A D).prod (colSplit_mp ν D A D)
  exact h2.comp h1

end GlobalTheory.BlockVolume

theorem GlobalTheory.blockVolume_prod : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (A D : Type) [Fintype A] [Fintype D] (S₁₁ : Set (Matrix A A k)) (S₁₂ : Set (Matrix A D k))
    (S₂₁ : Set (Matrix D A k)) (S₂₂ : Set (Matrix D D k)),
    volM ν (A ⊕ D) (A ⊕ D)
        {x | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      volM ν A A S₁₁ * volM ν A D S₁₂ * volM ν D A S₂₁ * volM ν D D S₂₂ := by
  intro k _ _ _ _ _ _ ν _ A D _ _ S₁₁ S₁₂ S₂₁ S₂₂
  haveI := GlobalTheory.IndexVolume.secondCountable k
  haveI : SigmaFinite ν := inferInstance
  haveI hσ : ∀ (m n : Type) [Fintype m] [Fintype n], SigmaFinite (volM ν m n) := fun m n _ _ => by
    exact (inferInstance : SigmaFinite (Measure.pi fun _ : m => Measure.pi fun _ : n => ν :
      Measure (m → n → k)))
  haveI := hσ A A; haveI := hσ A D; haveI := hσ D A; haveI := hσ D D
  have hmp := GlobalTheory.BlockVolume.blockSplit_mp ν A D
  have hset : {x : Matrix (A ⊕ D) (A ⊕ D) k | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧
      x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      GlobalTheory.BlockVolume.blockEquiv (k := k) A D ⁻¹' ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂)) := by
    ext x
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hset]
  have h := hmp.measure_preimage_equiv ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂))
  refine h.trans ?_
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockVolumeProdStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volM_blocks_eq_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (A D : Type) [Fintype A] [Fintype D] (S₁₁ : Set (Matrix A A k)) (S₁₂ : Set (Matrix A D k))
    (S₂₁ : Set (Matrix D A k)) (S₂₂ : Set (Matrix D D k)),
    volM ν (A ⊕ D) (A ⊕ D)
        {x | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      volM ν A A S₁₁ * volM ν A D S₁₂ * volM ν D A S₂₁ * volM ν D D S₂₂ := by
  first | exact @GlobalTheory.blockVolume_prod | exact GlobalTheory.blockVolume_prod | (intros; apply GlobalTheory.blockVolume_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalForallMapMem
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.KHomFinite

theorem isKC_Eab_of_sameBlock {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  unfold Eab
  rw [Matrix.single_apply]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    exact absurd h hcd
  · rfl

theorem sameBlock_self {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> first | trivial | exact h.elim

theorem map_mem_hwSub {p q : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (act' : Mat p q →ₗ[ℂ] Module.End ℂ V')
    (φ : V →ₗ[ℂ] V') (hφ : ∀ Z, IsKC Z → ∀ v, φ (act Z v) = act' Z (φ v))
    (μ : Ix p q → ℚ) (v : V) (hv : v ∈ hwSub act μ) : φ v ∈ hwSub act' μ := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
  obtain ⟨hw, hhi⟩ := hv
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [← hφ _ (isKC_Eab_of_sameBlock (sameBlock_self a)), ← map_smul, ← map_sub, hw a, map_zero]
  · rw [← hφ _ (isKC_Eab_of_sameBlock (sameBlock_of_posC hab)), hhi a b hab, map_zero]

theorem kStable_sup {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {A B : Submodule ℂ V} (hA : KStable act A)
    (hB : KStable act B) : KStable act (A ⊔ B) := by
  intro X hX w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hA X hX y hy) (hB X hX z hz)

theorem exists_kStable_ge {p q : ℕ} (M : GKMod p q) (H : Submodule ℂ M.V)
    (hH : FiniteDimensional ℂ H) :
    ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ H ≤ E ∧ KStable M.act E := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional H).mpr hH
  have key : ∀ t : Finset M.V, ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧
      Submodule.span ℂ (t : Set M.V) ≤ E ∧ KStable M.act E := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · refine ⟨⊥, inferInstance, by simp, ?_⟩
      intro X _ w hw
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw, map_zero]
    · intro x t _ ih
      obtain ⟨E₁, hE₁, hx, hK₁⟩ := M.kfin x
      obtain ⟨E₂, hE₂, ht, hK₂⟩ := ih
      refine ⟨E₁ ⊔ E₂, inferInstance, ?_, kStable_sup hK₁ hK₂⟩
      rw [Finset.coe_insert, Submodule.span_insert]
      exact sup_le_sup ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) ht
  obtain ⟨E, hE, hsE, hK⟩ := key s
  refine ⟨E, hE, ?_, hK⟩
  rw [← hs]
  exact hsE

theorem exists_finiteDimensional_forall_map_mem :
    ∀ (p q : ℕ) (M : GKMod p q), AdmGK M → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ ∀ φ : V →ₗ[ℂ] M.V, (∀ Z, IsKC Z → ∀ v, φ (act Z v) = M.act Z (φ v)) → ∀ v ∈ W, φ v ∈ E := by
  intro p q M hM V _ _ act hact W hW hWK hWwt
  suffices key : ∀ n : ℕ, ∀ U : Submodule ℂ V, U ≤ W → KStable act U → Module.finrank ℂ U = n →
      ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ ∀ φ : V →ₗ[ℂ] M.V,
        (∀ Z, IsKC Z → ∀ v, φ (act Z v) = M.act Z (φ v)) → ∀ v ∈ U, φ v ∈ E from
    key _ W le_rfl hWK rfl
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih U hUW hUK hn
  have hUfd : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUW
  obtain ⟨hsplit, hhw, -, -⟩ := GlobalTheory.T.glBlock_finiteDim_module_structure p q V act hact U hUfd hUK
    (fun v hv => hWwt v (hUW hv))
  by_cases hU0 : U = ⊥
  · refine ⟨⊥, inferInstance, fun φ _ v hv => ?_⟩
    rw [hU0, Submodule.mem_bot] at hv
    rw [hv, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨μ, v, hvU, hv⟩ := hhw hU0
  set N : Submodule ℂ V := sInf {N | v ∈ N ∧ KStable act N} with hN
  have hNK : KStable act N := by
    intro X hX w hw
    rw [Submodule.mem_sInf] at hw ⊢
    intro N' hN'
    exact hN'.2 X hX w (hw N' hN')
  have hvN : v ∈ N := Submodule.mem_sInf.mpr fun N' hN' => hN'.1
  have hNU : N ≤ U := sInf_le ⟨hvU, hUK⟩
  obtain ⟨U', hU'K, hdisj, hsup⟩ := hsplit N hNU hNK
  have hU'U : U' ≤ U := by
    rw [← hsup]
    exact le_sup_right
  have hvU' : v ∉ U' := by
    intro h
    have hmem : v ∈ N ⊓ U' := ⟨hvN, h⟩
    rw [hdisj, Submodule.mem_bot] at hmem
    exact hv.1 hmem
  have hlt : Module.finrank ℂ U' < n := by
    rw [← hn]
    exact Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne hU'U fun h => hvU' (by rw [h]; exact hvU))
  obtain ⟨E', hE', hE'mem⟩ := ih _ hlt U' (hU'U.trans hUW) hU'K rfl
  obtain ⟨Eμ, hEμ, hle, hEμK⟩ := exists_kStable_ge M (hwSub M.act μ) (hM μ)
  refine ⟨Eμ ⊔ E', inferInstance, fun φ hφ w hw => ?_⟩
  have hNφ : N ≤ Submodule.comap φ Eμ := by
    refine sInf_le ⟨?_, ?_⟩
    · exact hle (map_mem_hwSub act M.act φ hφ μ v hv.2)
    · intro X hX x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [hφ X hX x]
      exact hEμK X hX _ hx
  rw [← hsup] at hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hNφ hx) (hE'mem φ hφ y hy)

end GlobalTheory.KHomFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.FockAlg

theorem fock_structure : ∀ X : ProvA, admH2 X := by
  intro X p q r s
  refine ⟨fun d μ P hP hw => (GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector p q r s).1 d μ P hP hw.1 hw.2.1,
    fun d μ P hP hw => (GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector p q r s).2 d μ P hP hw.1 hw.2.1,
    fun μ P h0 ht hh => (GlobalTheory.T.fockHarmonic_homogeneous_of_KType p q r s).1 μ P h0 ht hh,
    fun μ P h0 ht hh => (GlobalTheory.T.fockHarmonic_homogeneous_of_KType p q r s).2 μ P h0 ht hh,
    fun μ μ' => ⟨GlobalTheory.T.finrank_fockJointHarmonics_highestWeight_of_shape p q r s μ μ', GlobalTheory.T.fockJointHarmonics_highestWeight_eq_bot_of_not_shape p q r s μ μ'⟩, ?_⟩
  intro u1 u2 hu d
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.fischerDecomposition_fockNoncompactParts p q r s d
  cases u1 <;> cases u2
  · simp at hu
  · have e1 : lowKer X (X.fock p q r s) false true = harm1 p q r s := by
      ext P; simp [lowKer, harm1, FockData.act2]
    have e2 : raised X (X.fock p q r s) false true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act2]
    rw [e1, e2]; exact h2
  · have e1 : lowKer X (X.fock p q r s) true false = harm2 p q r s := by
      ext P; simp [lowKer, harm2, FockData.act1]
    have e2 : raised X (X.fock p q r s) true false d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1]
    rw [e1, e2]; exact h1
  · have e1 : lowKer X (X.fock p q r s) true true = jointHarm p q r s := by
      ext P; simp [lowKer, jointHarm, harm1, harm2, FockData.act1, FockData.act2]
    have e2 : raised X (X.fock p q r s) true true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨
          ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1, FockData.act2]
    rw [e1, e2]; exact h3

end GlobalTheory.FockAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmul
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.CoefScale

lemma weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m t = ∑ a : Fin r, m (a, t) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type_right]
  rw [Finset.sum_eq_single t]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW]
  · intro s _ hs
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hs]
  · simp

theorem rowAct_scalar_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (c : ℂ) (F : MvPolynomial (Fin r × Fin n) ℂ)
    (hF : F ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ r n ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin r => c) F = c ^ (∑ t, ν t) • F := by
  have hw : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hF).1
  ext m
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul]
  by_cases h : AddMonoidAlgebra.coeff F m = 0
  · simp [h]
  · have hm := hw h
    rw [Finset.prod_pow_eq_pow_sum, mul_comm]
    congr 2
    simp only [Formalism.GradedWeylDivisibility.rowDeg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← weight_colW_apply, hm]

end GlobalTheory.CoefScale

namespace GlobalTheory

theorem blockAct_diag_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ)
    (Q : Formalism.L2.DIV.Pol ℂ ι n) (hQ : Q ∈ Formalism.L2.DIV.VV ℂ lam) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q =
      (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hQ
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have h1 := (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => Matrix.diagonal fun _ : Fin n => c τ)).1
    rw [map_prod]
    simp_rw [h1]
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin n => c τ) (F τ) =
        c τ ^ (∑ a, (lam τ).natW a) • F τ := fun τ =>
      GlobalTheory.CoefScale.rowAct_scalar_dualWeyl _ _ _ (hF τ)
    simp_rw [h2, map_smul, Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmulStatement
open Formalism.L2.Ker MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockAction_diagonal_coefficientSpace_smul : ∀ {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ) (Q : Formalism.L2.DIV.Pol ℂ ι n), Q ∈ Formalism.L2.DIV.VV ℂ lam → Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q = (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  first | exact @GlobalTheory.blockAct_diag_mem_VV | exact GlobalTheory.blockAct_diag_mem_VV | (intros; apply GlobalTheory.blockAct_diag_mem_VV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaJetMapWeightedTableScale
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaJetMapWeightedTableScale
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.JetScale

section General

variable {σ : Type} [Fintype σ]

def scaleVar (w : σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => C (w v) * X v

lemma monomial_eq_prod (s : σ →₀ ℕ) (r : ℂ) :
    (monomial s r : MvPolynomial σ ℂ) = C r * ∏ v, X v ^ s v := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

lemma scaleVar_monomial (w : σ → ℂ) (s : σ →₀ ℕ) (r : ℂ) :
    scaleVar w (monomial s r) = monomial s (r * ∏ v, w v ^ s v) := by
  rw [monomial_eq_prod, monomial_eq_prod, scaleVar, map_mul, aeval_C, map_prod, map_mul C, map_prod C]
  simp only [map_pow, aeval_X, mul_pow, Finset.prod_mul_distrib, algebraMap_eq]
  ring

end General

section Jet

variable {ι : Type} [Fintype ι] {a b : ℕ}

lemma jetLin_monomial (J : (DVar ι a b →₀ ℕ) → ℂ) (m : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (r : ℂ) :
    jetLin J (monomial m r) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (r * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h : (monomial m r : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) =
      r • basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

def wDer (c : ι → ℂ) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℂ := Sum.elim (fun _ => 1) (fun k => c k.1)

def wCoord (c : ι → ℂ) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℂ := Sum.elim (fun k => c k.1) (fun _ => 1)

lemma jetLin_scaleDer (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin J (scaleVar (wDer c) Q) = jetLin (fun m => (∏ k, c k.1 ^ m k) * J m) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [scaleVar_monomial, jetLin_monomial, jetLin_monomial, Fintype.prod_sum_type]
    simp [wDer, Finsupp.comapDomain_apply]
    congr 1
    ring
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

lemma blockAct_diag (c : ι → ℂ) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (n := b) (fun τ => Matrix.diagonal fun _ : Fin b => c τ) = scaleVar (fun v : ι × Fin b × Fin b => c v.1) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [Formalism.GradedWeylDivisibility.blockAct, scaleVar, Matrix.diagonal_apply, apply_ite C, ite_mul, Finset.sum_ite_eq]

lemma jetLin_scaleCoord (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin J (scaleVar (wCoord c) Q) = scaleVar (fun v : ι × Fin b × Fin b => c v.1) (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [scaleVar_monomial, jetLin_monomial, jetLin_monomial, scaleVar_monomial, Fintype.prod_sum_type]
    simp [wCoord, Finsupp.comapDomain_apply]
    congr 1
    ring
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

lemma scale_subD (c : ι → ℂ) :
    (scaleVar (wDer (a := a) (b := b) c)).comp (subD ℂ ι a b) = (scaleVar (wCoord c)).comp (subD ℂ ι a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, subD, aeval_X]
  split_ifs
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, scaleVar, aeval_X, wDer, wCoord, Sum.elim_inl, Sum.elim_inr, map_one, one_mul]
      refine Finset.sum_congr rfl fun β _ => ?_
      ring
  · simp

lemma jetLin_smul_table (u : ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin (fun m => u * J m) Q = u • jetLin J Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [jetLin_monomial, jetLin_monomial, smul_monomial, smul_eq_mul]
    congr 1
    ring
  | add p q hp hq => simp only [map_add (f := _), hp, hq, smul_add]

end Jet

theorem jetMap_weight_scale {ι : Type} [Fintype ι] {a b : ℕ} (u : ℂ) (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ)
    (P : Formalism.L2.DIV.Pol ℂ ι a) :
    jetMap (fun m => u * ((m.prod fun k e => c k.1 ^ e) * J m)) nn P =
      u • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin b => c τ) (jetMap J nn P) := by
  have hJ : (fun m : DVar ι a b →₀ ℕ => u * ((m.prod fun k e => c k.1 ^ e) * J m)) =
      fun m => u * ((∏ k, c k.1 ^ m k) * J m) := by
    funext m
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [hJ, blockAct_diag]
  rw [jetMap, jetMap, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply]
  have key := DFunLike.congr_fun (scale_subD (a := a) (b := b) c) (LinearMap.mulRight ℂ (∏ τ, frDet ℂ a τ ^ nn τ) P)
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at key
  rw [jetLin_smul_table, ← jetLin_scaleDer, key, jetLin_scaleCoord]

end GlobalTheory.JetScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaJetMapWeightedTableScaleStatement
open Formalism.L2.Ker MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaJetMap_weighted_table_scale : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (u : ℂ) (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ) (P : Formalism.L2.DIV.Pol ℂ ι a), jetMap (fun m => u * ((m.prod fun k e => c k.1 ^ e) * J m)) nn P = u • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin b => c τ) (jetMap J nn P) := by
  first | exact @GlobalTheory.JetScale.jetMap_weight_scale | exact GlobalTheory.JetScale.jetMap_weight_scale | (intros; apply GlobalTheory.JetScale.jetMap_weight_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDualWeylOfUnitriangularFixed
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem matRep_diagGL_monomial_colChar {n n' : ℕ} (t : Fin n → ℂˣ) (d : Fin n' × Fin n →₀ ℕ) (c : ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (monomial d c) =
      monomial d ((d.prod fun x e => (t x.2 : ℂ) ^ e) * c) := by
  have h : sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
      ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ =
      aeval (fun x : Fin n' × Fin n => C (t x.2 : ℂ) * (X x : MvPolynomial (Fin n' × Fin n) ℂ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, diagGL, Fintype.sum_prod_type, Matrix.one_apply, Matrix.diagonal_apply, apply_ite C]
  rw [matRep_apply, h, aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, algebraMap_eq]
  ring

theorem coeff_matRep_diagGL_colChar {n n' : ℕ} (t : Fin n → ℂˣ) (v : MvPolynomial (Fin n' × Fin n) ℂ)
    (d : Fin n' × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (matRep n n' (diagGL ℂ n t, 1) v) d = (d.prod fun x e => (t x.2 : ℂ) ^ e) * AddMonoidAlgebra.coeff v d := by
  classical
  induction v using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [matRep_diagGL_monomial_colChar, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem colAdd_eq_matRep_of_transvection {n n' : ℕ} (l j : Fin n) (c : ℂ) (g : GL (Fin n) ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = Matrix.transvection l j c)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) : colAdd ℂ l j c v = matRep n n' (g, 1) v := by
  have h : sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
      (g : Matrix (Fin n) (Fin n) ℂ))ᵀ = colAdd ℂ (r := n') l j c := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    rw [hg]
    by_cases hs : s = j
    · subst hs
      simp [sub, colAdd, Fintype.sum_prod_type, Matrix.one_apply, Matrix.transvection, Matrix.single_apply,
        apply_ite C, add_mul, Finset.sum_add_distrib]
    · have hs' : ¬ j = s := fun e => hs e.symm
      simp [sub, colAdd, Fintype.sum_prod_type, Matrix.one_apply, Matrix.transvection, Matrix.single_apply,
        apply_ite C, hs, hs']
  rw [matRep_apply, h]

theorem mem_dualWeyl_of_unitriangular_fixed :
    ∀ (n n' : ℕ) (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), (∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id → (∀ a, (g : Matrix (Fin n) (Fin n) ℂ) a a = 1) → matRep n n' (g, 1) v = v) → (∀ t : Fin n → ℂˣ, matRep n n' (diagGL ℂ n t, 1) v = (∏ a, (t a : ℂ) ^ ν a) • v) → v ∈ dualWeyl ℂ n' n ν := by
  intro n n' ν v hU hT
  rw [Formalism.GradedWeylDivisibility.dualWeylPoint ℂ n' n ν v]
  refine ⟨fun d hd => ?_, fun l j hlj c => ?_⟩
  · funext i
    let t : Fin n → ℂˣ := fun s => if s = i then Units.mk0 2 two_ne_zero else 1
    have h1 := congrArg (AddMonoidAlgebra.coeff · d) (hT t)
    rw [coeff_matRep_diagGL_colChar, coeff_smul, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hd h1
    have h3 : (∏ a, (t a : ℂ) ^ ν a) = 2 ^ ν i := by
      rw [Finset.prod_eq_single i]
      · simp [t]
      · intro b _ hb
        simp [t, hb]
      · simp
    have h4 : (d.prod fun x e => (t x.2 : ℂ) ^ e) = 2 ^ (Finsupp.weight (colW n' n) d i) := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      by_cases hx : x.2 = i
      · simp [t, colW, hx]
      · simp [t, colW, hx]
    rw [h3, h4] at h2
    have h5 : (2 : ℕ) ^ (Finsupp.weight (colW n' n) d i) = 2 ^ ν i := by exact_mod_cast h2
    exact Nat.pow_right_injective le_rfl h5
  · have hne : l ≠ j := hlj.ne
    let g : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection l j c)
      (by rw [Matrix.det_transvection_of_ne l j hne]; exact one_ne_zero)
    have hg : (g : Matrix (Fin n) (Fin n) ℂ) = Matrix.transvection l j c := rfl
    rw [colAdd_eq_matRep_of_transvection l j c g hg]
    refine hU g ?_ ?_
    · intro a b hab
      have hab' : b < a := hab
      have h1 : ¬ (l = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hlj hab'
      rw [hg]
      simp [Matrix.transvection, h1, Matrix.one_apply_ne hab'.ne']
    · intro a
      have h1 : ¬ (l = a ∧ j = a) := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      rw [hg]
      simp [Matrix.transvection, h1]

end GlobalTheory.GLDuality
end
