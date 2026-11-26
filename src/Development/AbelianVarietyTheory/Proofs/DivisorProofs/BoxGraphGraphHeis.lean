module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharInfinityEqCoeffMulHalfNormPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat.GraphHeis

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem isHalf_nsmul' {m n : ℕ} {ε : AE D} {a : Mx D m n} (ha : IsHalf ε a) (k : ℕ) : IsHalf ε (k • a) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, ha i j]

theorem isHalf_of_add' {m n : ℕ} {ε : AE D} {a b : Mx D m n} (h : IsHalf ε (a + b)) (hb : IsHalf ε b) : IsHalf ε a :=
  fun i j => by
    have h1 := h i j
    rw [Matrix.add_apply, mul_add, hb i j] at h1
    exact add_right_cancel h1

theorem sb_trans {m n : ℕ} {ε : AE D} {Λ : AddSubgroup (Mx D m n)} {φ : Mx D m n → ℂ} (h : IsSBHalf ε Λ φ)
    {x : Mx D m n} (hx : IsHalf ε x) {k₀ : ℕ} (hk₀ : 0 < k₀) (hkx : k₀ • x ∈ Λ) :
    IsSBHalf ε Λ (fun t => φ (t + x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => isHalf_of_add' (h1 _ ht) hx, k * k₀, Nat.mul_pos hk hk₀, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · show φ (t + (k * k₀) • u + x) = φ (t + x)
    rw [show t + (k * k₀) • u + x = (t + x) + k • (k₀ • u) by rw [mul_smul]; abel]
    exact h2 _ (nsmul_mem hu k₀) (isHalf_nsmul' hu' k₀) _
  · have e : (k * k₀) • t = k₀ • (k • (t + x)) - k • (k₀ • x) := by
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, mul_comm k₀ k]; abel
    rw [e]
    exact sub_mem (nsmul_mem (h3 _ ht) k₀) (nsmul_mem hkx k)

theorem sb_modul {m n : ℕ} {ε : AE D} {Λ : AddSubgroup (Mx D m n)} {φ : Mx D m n → ℂ} (h : IsSBHalf ε Λ φ)
    (χ : Mx D m n → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (h1χ : ∀ u ∈ Λ, IsHalf ε u → χ (k₀ • u) = 1) : IsSBHalf ε Λ (fun t => χ t * φ t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k₀ * k, Nat.mul_pos hk₀ hk, fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · show χ (t + (k₀ * k) • u) * φ (t + (k₀ * k) • u) = χ t * φ t
    rw [hχ, mul_smul, h1χ _ (nsmul_mem hu k) (isHalf_nsmul' hu' k), mul_one, smul_comm k₀ k u,
      h2 _ (nsmul_mem hu k₀) (isHalf_nsmul' hu' k₀)]
  · rw [mul_smul]
    exact nsmul_mem (h3 t (right_ne_zero_of_mul ht)) k₀

theorem symplO_add_left' (S T : HSp D) (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, LinearMap.map_add (f := _)]

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, RingHom.map_add (f := _), map_add (cA D), mul_add, add_mul, Finset.sum_add_distrib,
    LinearMap.map_add]

theorem symplO_nsmul' (S T : HSp D) (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  have h1 := map_nsmul (AddMonoidHom.mk' (fun x => symplO S T x y) fun a b => symplO_add_left' S T a b y) k x
  have h2 := map_nsmul (AddMonoidHom.mk' (fun y => symplO S T x y) fun a b => symplO_add_right' S T x a b) k y
  exact h1.trans h2.symm

theorem map_infPart_of_half {S T : HSp D} {a : AE D} (ha : infPart D a = 0) {u : WO S T} (hu : IsHalf a u) :
    u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, map_mul, ha, zero_mul]

theorem sb_trans_latO {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : Submodule.IsFullLattice D.host.E ΛS)
    (hT : Submodule.IsFullLattice D.host.E ΛT) {ε : AE D} (hinf : infPart D ε = 0) {φ : WO S T → ℂ}
    (h : IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) φ)
    {x : WO S T} (hx : IsHalf ε x) :
    IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun t => φ (t + x)) := by
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS hT x (map_infPart_of_half hinf hx)
  exact sb_trans h hx hk hkx

theorem sb_modul_latO {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {ε : AE D} (hinf : infPart D (cA D ε) = 0) {φ : WO S T → ℂ}
    (h : IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) φ)
    {y : WO S T} (hy : IsHalf (cA D ε) y) :
    IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun t => ψ (symplO S T t y) * φ t) := by
  obtain ⟨k, hk, hky⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO
    (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) y (map_infPart_of_half hinf hy)
  refine sb_modul h (fun t => ψ (symplO S T t y)) (fun a b => ?_) hk (fun u hu _ => ?_)
  · show ψ (symplO S T (a + b) y) = ψ (symplO S T a y) * ψ (symplO S T b y)
    rw [symplO_add_left', AddChar.map_add_eq_mul]
  · show ψ (symplO S T (k • u) y) = 1
    rw [symplO_nsmul']
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hu hky

end GlobalTheory.BigDat.GraphHeis

namespace GlobalTheory.BigDat

open GlobalTheory.BigDat.GraphHeis

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

def graphMap (e : Num G i j) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) : (Pt G i j → ℂ) →ₗ[ℂ] (Pt G i j → ℂ) where
  toFun g u := T₁ (fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u)) (mapV e u)
  map_add' g g' := funext fun u => by
    have h : (fun x => T₂ (fun y => (g + g') (ofMaps e (x, y))) (mapW e u)) =
        (fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u)) + fun x => T₂ (fun y => g' (ofMaps e (x, y))) (mapW e u) :=
      funext fun x => by
        show T₂ ((fun y => g (ofMaps e (x, y))) + fun y => g' (ofMaps e (x, y))) (mapW e u) = _
        rw [map_add (f := _)]; rfl
    show T₁ (fun x => T₂ (fun y => (g + g') (ofMaps e (x, y))) (mapW e u)) (mapV e u) = _
    rw [h, map_add (f := _)]; rfl
  map_smul' c g := funext fun u => by
    have h : (fun x => T₂ (fun y => (c • g) (ofMaps e (x, y))) (mapW e u)) =
        c • fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u) :=
      funext fun x => by
        show T₂ (c • fun y => g (ofMaps e (x, y))) (mapW e u) = _
        rw [map_smul]; rfl
    show T₁ (fun x => T₂ (fun y => (c • g) (ofMaps e (x, y))) (mapW e u)) (mapV e u) = _
    rw [h, map_smul]; rfl

theorem graphMap_box (e : Num G i j) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) (φ₁ : HomV G i j → ℂ) (φ₂ : HomW G i j → ℂ) :
    graphMap e T₁ T₂ (box e φ₁ φ₂) = box e (T₁ φ₁) (T₂ φ₂) := funext fun u => by
  have e2 : ∀ x, (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) = φ₁ x • φ₂ := fun x => funext fun y => by
    show φ₁ (mapV e (ofMaps e (x, y))) * φ₂ (mapW e (ofMaps e (x, y))) = φ₁ x * φ₂ y
    rw [mapV_ofMaps, mapW_ofMaps]
  have e1 : (fun x => T₂ (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) (mapW e u)) = T₂ φ₂ (mapW e u) • φ₁ :=
    funext fun x => by
      rw [e2, map_smul]
      show φ₁ x * T₂ φ₂ (mapW e u) = T₂ φ₂ (mapW e u) * φ₁ x
      exact mul_comm _ _
  show T₁ (fun x => T₂ (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) (mapW e u)) (mapV e u) = T₁ φ₁ (mapV e u) * T₂ φ₂ (mapW e u)
  rw [e1, map_smul]
  show T₂ φ₂ (mapW e u) * T₁ φ₁ (mapV e u) = _
  exact mul_comm _ _

def transPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (x : Pt G i j) :
    ((Pt G i j → ℂ) × (Pt G i j → ℂ)) →ₗ[ℂ] ((Pt G i j → ℂ) × (Pt G i j → ℂ)) where
  toFun p := (fun u => p.1 (u + x), heisPt Γ ψ x p.2)
  map_add' p q := Prod.ext rfl (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext rfl (funext fun u => mul_left_comm _ _ _)

def modulPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (y : Pt G i j) :
    ((Pt G i j → ℂ) × (Pt G i j → ℂ)) →ₗ[ℂ] ((Pt G i j → ℂ) × (Pt G i j → ℂ)) where
  toFun p := (fun u => ψ (sympPt Γ u y) * p.1 u, heisPt Γ ψ y p.2)
  map_add' p q := Prod.ext (funext fun u => mul_add _ _ _) (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext (funext fun u => mul_left_comm _ _ _) (funext fun u => mul_left_comm _ _ _)

end GlobalTheory.BigDat


set_option maxHeartbeats 1600000 in
open GlobalTheory.BigDat.GraphHeis in
theorem GlobalTheory.BigDat.boxGraph_graph_heis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e → ∀ (ε : AE D) (P : Finset (Pl D.host.E)), IsIdemSum ε P →
    ∀ (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
      (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)),
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latV G i j) 1 f₁ T₁ →
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latW G i j) 1 f₂ T₂ →
    (∀ f, (0, f) ∈ boxGraph e ε T₁ T₂ → f = 0) ∧
    (∀ x ∈ mixHalf e ε, ∀ p ∈ boxGraph e ε T₁ T₂, (fun u => p.1 (u + x), heisPt Γ W.ψ x p.2) ∈ boxGraph e ε T₁ T₂) ∧
    ∀ y ∈ mixHalf e (cA D ε), ∀ p ∈ boxGraph e ε T₁ T₂,
      (fun u => W.ψ (sympPt Γ u y) * p.1 u, heisPt Γ W.ψ y p.2) ∈ boxGraph e ε T₁ T₂ := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW ε P hε f₁ f₂ T₁ T₂ h₁ h₂
  have hinf : infPart D ε = 0 := GlobalTheory.PlaceVec.idemSum_infPart hε
  have hinf' : infPart D (cA D ε) = 0 := GlobalTheory.PlaceVec.infPart_cA hinf
  have sdW : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have sdV : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have sdV₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have sdW' : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) := isSelfDualC_neg sdW
  refine ⟨fun f hf => ?_, fun x hx p hp => ?_, fun y hy p hp => ?_⟩
  · have key : boxGraph e ε T₁ T₂ ≤ LinearMap.ker (LinearMap.snd ℂ _ _ - graphMap e T₁ T₂ ∘ₗ LinearMap.fst ℂ _ _) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, -, -, rfl⟩ := hp
      show box e (T₁ φ₁) (T₂ φ₂) - graphMap e T₁ T₂ (box e φ₁ φ₂) = 0
      rw [graphMap_box, sub_self]
    have h0 := key hf
    rw [LinearMap.mem_ker] at h0
    have h1 : f - graphMap e T₁ T₂ 0 = 0 := h0
    rwa [map_zero, sub_zero] at h1
  · have key : boxGraph e ε T₁ T₂ ≤ (boxGraph e ε T₁ T₂).comap (transPair Γ W.ψ x) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hx₁ : IsHalf ε (mapV e x) := hx.1
      have hx₂ : IsHalf ε (mapW e x) := hx.2
      have s₁ : IsSBHalf ε (latV G i j) (fun t => φ₁ (t + mapV e x)) :=
        sb_trans_latO (S := negSp (spW G i j)) (T := spV G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) (GlobalTheory.PlaceVec.selfDual_isFullLattice (negSp (spW G i j)) _ sdW')
          (GlobalTheory.PlaceVec.selfDual_isFullLattice (spV G i j) _ sdV) hinf hφ₁ hx₁
      have s₂ : IsSBHalf ε (latW G i j) (fun t => φ₂ (t + mapW e x)) :=
        sb_trans_latO (S := spV₁ G i j) (T := spW G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) (GlobalTheory.PlaceVec.selfDual_isFullLattice (spV₁ G i j) _ sdV₁)
          (GlobalTheory.PlaceVec.selfDual_isFullLattice (spW G i j) _ sdW) hinf hφ₂ hx₂
      show (fun u => box e φ₁ φ₂ (u + x), heisPt Γ W.ψ x (box e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph e ε T₁ T₂
      rw [heisPt_box e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.trans φ₁ hφ₁ _ hx₁, h₂.trans φ₂ hφ₂ _ hx₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show φ₁ (mapV e (u + x)) * φ₂ (mapW e (u + x)) = φ₁ (mapV e u + mapV e x) * φ₂ (mapW e u + mapW e x)
      rw [mapV_add, mapW_add]
    exact key hp
  · have key : boxGraph e ε T₁ T₂ ≤ (boxGraph e ε T₁ T₂).comap (modulPair Γ W.ψ y) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hy₁ : IsHalf (cA D ε) (mapV e y) := hy.1
      have hy₂ : IsHalf (cA D ε) (mapW e y) := hy.2
      have s₁ : IsSBHalf ε (latV G i j) (fun t => W.ψ (symplO _ _ t (mapV e y)) * φ₁ t) :=
        sb_modul_latO (S := negSp (spW G i j)) (T := spV G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) W.ψ_std sdW' sdV hinf' hφ₁ hy₁
      have s₂ : IsSBHalf ε (latW G i j) (fun t => W.ψ (symplO _ _ t (mapW e y)) * φ₂ t) :=
        sb_modul_latO (S := spV₁ G i j) (T := spW G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) W.ψ_std sdV₁ sdW hinf' hφ₂ hy₂
      show (fun u => W.ψ (sympPt Γ u y) * box e φ₁ φ₂ u, heisPt Γ W.ψ y (box e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph e ε T₁ T₂
      rw [heisPt_box e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.modul φ₁ hφ₁ _ hy₁, h₂.modul φ₂ hφ₂ _ hy₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show W.ψ (sympPt Γ u y) * (φ₁ (mapV e u) * φ₂ (mapW e u)) =
        (W.ψ (symplO _ _ (mapV e u) (mapV e y)) * φ₁ (mapV e u)) * (W.ψ (symplO _ _ (mapW e u) (mapW e y)) * φ₂ (mapW e u))
      rw [symp_eq e Γ hW hWW, AddChar.map_add_eq_mul]
      ring
    exact key hp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewGramInrInl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat.VacFix

theorem isHalf_of_mulG {D : D7} (S : HSp D) {n : ℕ} (ε : AE D) (x : Matrix (Fin n) (Fin S.rank) (AE D))
    (h : ∀ a b, ε * mulG S x a b = mulG S x a b) (a : Fin n) (b : Fin S.rank) : ε * x a b = x a b := by
  have h1 : ε • mulG S x = mulG S x := Matrix.ext h
  have h2 : divG S (ε • mulG S x) = ε • divG S (mulG S x) := Matrix.smul_mul _ _ _
  rw [h1, divG_mulG] at h2
  exact (congrFun (congrFun h2 a) b).symm

theorem hTens_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (hc : ∀ a, c (c a) = a)
    {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A)
    (h₁ : ∀ a b, JB (e (.inl a)) (e (.inr b)) = 0) (h₂ : ∀ a b, JB (e (.inr a)) (e (.inl b)) = 0)
    (ε : A) (hε : ε * c ε = 0) (x : Matrix (Fin n) (Fin d) A)
    (hl : ∀ a b, ε * x a (e (.inl b)) = x a (e (.inl b)))
    (hr : ∀ a b, ε * c (x a (e (.inr b))) = c (x a (e (.inr b)))) : hTens c JA JB x x = 0 := by
  unfold hTens
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  obtain ⟨b | b, rfl⟩ := e.surjective b <;> obtain ⟨l | l, rfl⟩ := e.surjective l
  · have u := congrArg c (hl k l)
    rw [map_mul] at u
    rw [← u, ← hl a b]
    linear_combination (x a (e (.inl b)) * JA a k * JB (e (.inl b)) (e (.inl l)) * c (x k (e (.inl l)))) * hε
  · rw [h₁, mul_zero, zero_mul]
  · rw [h₂, mul_zero, zero_mul]
  · have u := congrArg c (hr a b)
    rw [map_mul, hc] at u
    rw [← u, ← hr k l]
    linear_combination (x a (e (.inr b)) * JA a k * JB (e (.inr b)) (e (.inr l)) * c (x k (e (.inr l)))) * hε

theorem skewGram_inl_inr {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (a b) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e (e (.inl a)) (e (.inr b)) = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem skewGram_inr_inl {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (a b) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e (e (.inr a)) (e (.inl b)) = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem hTens_mixHalf {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (ε : AE D)
    (hε : ε * cA D ε = 0) (γ : Pt G i j) (hγ : γ ∈ mixHalf e ε) :
    hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ = 0 := by
  refine hTens_eq_zero (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) GlobalTheory.DualPairCheck.cA_cA e _ _
    (fun a b => ?_) (fun a b => ?_) ε hε γ (fun a b => ?_) (fun a b => ?_)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (skewGram_inl_inr _ _ e a b))).trans (map_zero _)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (skewGram_inr_inl _ _ e a b))).trans (map_zero _)
  · exact isHalf_of_mulG (negSp (spW G i j)) ε (colV e γ)ᵀ hγ.1 b a
  · refine isHalf_of_mulG (spV₁ G i j) ε ((γ.submatrix id fun k => e (.inr k)).map (cA D)) (fun a b => ?_) a b
    exact neg_injective ((mul_neg _ _).symm.trans (hγ.2 a b))

theorem psi_double {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ)
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (θ : 𝓞 E)
    (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hγ : γ ∈ latAtV X Y v) :
    B.ψ (⅟(2 : AF F) * symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (2 • γ) (2 • γ)) = 1 := by
  have h2 : (2 : ℕ) • γ = (2 : AF F) • γ := by rw [two_smul, two_smul]
  rw [h2, GlobalTheory.LatVac.symp_smul_smul, ← mul_assoc, ← mul_assoc, invOf_mul_self, one_mul]
  refine GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 2 ?_ γ hγ γ hγ
  rw [map_ofNat]
  exact ofNat_mem _ 2

theorem vac_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ v : Pl D.host.F, (∀ u ∈ latPt e v, u ∈ latAtV Γ.V Γ.W v) →
      ∀ γ ∈ genPt e v, Acts (evFin D.host.F v) (Γ.M.co.rho W.ψ γ) (Γ.M.vac v) (Γ.M.vac v) := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT v hL γ hγ
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM.vac v
  have h1 := hθ γ (hL γ (genPt_subset e v hγ))
  have h2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) = 1 := by
    rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, ε, hε, hγ⟩
    · exact psi_double _ Bs Γ.V Γ.W _ _ _ _ hT.base hT.geo.hV hT.geo.hW v θ γ' (hL γ' hγ')
    · unfold symp
      rw [hTens_mixHalf e Γ h.JWW ε hε.2.1 γ hγ, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]
  rw [h2, one_smul, h.ψ] at h1
  exact h1

end GlobalTheory.BigDat.VacFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValues
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.SeriesTie
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.JoinChr (IsPlIdem locE)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DeltaFixed

theorem aut_fixes_delta_values : ∀ {D : D7} (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (χ : HChar D.host.E),
    ChrEq (ρ.B i j b).de.chi χ → χ.ValuesIn 0 (embLL0 D) → ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (embLL0 D y) = embLL0 D y) →
    ∀ σ, τ (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))) =
      ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  intro D ρ hρ i j b χ hχ hval τ hτ σ
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  set f : D.ntw.O0 i →+* ℂ := (ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)) with hf

  have hker : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := by
    cases b
    · have e : (ψ.ker : Set (G D.host.E D.nd.Om)) = ((D.ntw.delta i).ker : Set _) := by
        ext g
        simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
      rw [e]
      exact D.ntw.delta_open i
    · simpa [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt] using D.ntw.delta_open i

  have hram : ∀ v, v ∉ D.ntw.pD i → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ g ∈ Ine (F := D.host.E) A, ψ g = 1 := by
    intro v hv A hA g hg
    have h1 : D.ntw.delta i g = 1 := by
      by_contra h
      exact hv ((D.ntw.delta_ram i v A hA).1 ⟨g, hg, h⟩)
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h1]

  haveI : Finite (G D.host.E D.nd.Om ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hker
  have hn : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpow : ∀ g, ψ g ^ ψ.ker.index = 1 := fun g => by
    rw [← map_pow]
    exact (MonoidHom.mem_ker).1 (Subgroup.pow_index_mem _ g)

  have hchi : ChrEq (charOf ρ.rc f ψ) χ := by
    have := hχ
    rw [hρ.delta i j b] at this
    exact this

  let r' : G D.host.E D.nd.Om →* ℂˣ := (Units.map f.toMonoidHom).comp ψ
  let r : G D.host.E D.nd.Om →* ℂˣ := (Units.map ((τ : ℂ →+* ℂ).comp f).toMonoidHom).comp ψ
  have hr' : Continuous r' := GlobalTheory.DeltaGal.continuous_comp_of_isOpen_ker ψ hker (Units.map f.toMonoidHom)
  have hr : Continuous r := GlobalTheory.DeltaGal.continuous_comp_of_isOpen_ker ψ hker (Units.map ((τ : ℂ →+* ℂ).comp f).toMonoidHom)
  have hart : IsGlobalArtin ρ.rc.art := hρ.rc.artin
  obtain ⟨_, _, _, _, hidem, _⟩ := GlobalTheory.EtaProduct.exists_ev D
  have key : r = r' := by
    refine GlobalTheory.GalChar.eq_of_frob hart hr hr' ?_
    have h1 := GlobalTheory.GalChar.unr_ae χ
    have h2 : ∀ᶠ v in Filter.cofinite, v ∉ D.ntw.pD i :=
      Filter.eventually_cofinite.2 (by simpa using (D.ntw.pD i).finite_toSet)
    filter_upwards [h1, h2] with v hunr hv A hA s hs

    obtain ⟨x0, hx0, hx0a⟩ := (hart.frob v A hA (toAb D.host.E D.nd.Om s⁻¹)).2 ⟨s, hs, rfl⟩

    set k := unif v
    have hk : IsUnifAt v (atFin v k) := unif_spec v
    have hu : IsUnitAt v (x0 * (atFin v k)⁻¹) := by
      unfold IsUnitAt
      unfold IsUnifAt at hx0 hk
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx0, hk]
      exact mul_inv_cancel₀ (by simp)
    obtain ⟨t, ht, hta⟩ := GlobalTheory.GalChar.exists_ine hart hA hu
    have hψt : ψ t = 1 := hram v hv A hA t ht

    obtain ⟨e, he⟩ := hidem v
    let xe : (Formalism.L2.Theta.AE D)ˣ := (Formalism.L2.JoinChr.isUnit_locE he.1 k).unit
    have hxe : ρ.rc.sym xe = toAb D.host.E D.nd.Om (t⁻¹ * s⁻¹) := by
      have e1 : Units.map ρ.rc.κ.toMonoidHom xe = Neutral.B1.localIdele D.host.E v (atFin v k) := by
        apply Units.ext
        exact hρ.rc.loc v e he k
      have e2 : atFin v k = (x0 * (atFin v k)⁻¹)⁻¹ * x0 := by group
      change ρ.rc.art (Units.map ρ.rc.κ.toMonoidHom xe) = _
      rw [e1, e2, map_mul, map_mul, map_inv, map_inv, hta, hx0a, ← map_inv, ← map_mul]
    have hc := charOf_eq ρ.rc f hker hxe hn (hpow _)
    have hc2 := hchi.2 v e he k xe rfl
    have hloc : χ.locK v k = χ.val v := χ.val_eq hunr _ hk
    obtain ⟨y, hy⟩ := hval v hunr
    have hy' : embLL0 D y = ((χ.val v : ℂˣ) : ℂ) := by
      rw [hy, HChar.valTw]
      simp
    have hfs : f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = embLL0 D y⁻¹ := by
      have h3 : f ((ψ (t⁻¹ * s⁻¹) : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = embLL0 D y := by
        rw [← hc, hc2, hloc, hy']
      rw [map_mul, map_inv, map_inv, hψt, inv_one, one_mul, map_units_inv] at h3
      rw [map_inv₀, ← h3, inv_inv]
    apply Units.ext
    show τ (f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) = f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)
    rw [hfs]
    exact hτ _
  have := congrArg (fun φ : G D.host.E D.nd.Om →* ℂˣ => ((φ σ : ℂˣ) : ℂ)) key
  exact this

end GlobalTheory.DeltaFixed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValuesStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.SeriesTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values : ∀ {D : D7} (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (χ : HChar D.host.E),
    ChrEq (ρ.B i j b).de.chi χ → χ.ValuesIn 0 (embLL0 D) → ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (embLL0 D y) = embLL0 D y) →
    ∀ σ, τ (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))) =
      ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  first | exact @GlobalTheory.DeltaFixed.aut_fixes_delta_values | exact GlobalTheory.DeltaFixed.aut_fixes_delta_values | (intros; apply GlobalTheory.DeltaFixed.aut_fixes_delta_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OneMapAll


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.OnCmp.const_upTo_center : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ cc, GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, GlobalTheory.AdTh.SerOf (O i) (κ i) (v₀ i (sg0 D A)) (u • cc) 1 → ∃ z ∈ Subgroup.center G, ∃ (ζ : D.what₂.LL) (n : ℕ), 0 < n ∧ ζ ^ n = 1 ∧ ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ g, (O i).phi (u • cc) f g = D.what₂.embLL ζ * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (actLev T.J.toCore.Q.c (O i).lev2 z f) g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hpins hU hIo h0 hPh hSpan cc hcc u hser
  have hP := hpins.2
  obtain ⟨hE, ⟨hLL, -, -, hcU, -, z, hz, hrowT⟩, -⟩ := hPh h0
  obtain ⟨ζ, hζL, ⟨m, hm, hζm⟩, hT1⟩ := hrowT ()
  obtain ⟨ζ', rfl⟩ := (AlgHom.mem_fieldRange).1 hζL
  have hζ : D.what₂.embLL.toRatAlgHom ζ' = D.what₂.embLL ζ' := rfl
  rw [hζ] at hζm hT1
  clear hζL
  have hs0 : ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (lieFac_pos _ _ _).ne'
  have gen : ∀ x, (O i).Plc () x → ∀ Fr ∈ sec (T.J.Q.Xo ((i : ℕ) + 1)) (O i).c' (wtA (κ i)) (Vc D i).rank,
      IsSum (O i) () x Fr → ∀ q,
      ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * geo (O i) (u • cc) 1 Fr q =
        (D.what₂.embLL ζ' * ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ)) *
          geo (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z Fr q := by
    intro x hx Fr hF hsum q
    have h1 := (hT1 x hx).2 Fr hF hsum q
    obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple ()).reps
    obtain ⟨y, hy⟩ := (hPl x).1 hx
    have h2 := hser.2.2 () h J' hR _ x hy Fr hF hsum q.out
    have h3 : actLev (O i).c' (O i).lev2 1 Fr = Fr := actL_one _ _ _ hP.act.2.total hP.act.2.func hP.act.2.one hF.1
    rw [hA _ x hy] at h1
    unfold geo
    rw [h3]
    simp only [jFn, onQ, adel, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul, one_mul] at h1 h2 ⊢
    linear_combination h1 - h2
  have span : ∀ q, ∀ Fr ∈ cuspOver (O i) (κ i),
      ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * geo (O i) (u • cc) 1 Fr q =
        (D.what₂.embLL ζ' * ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ)) *
          geo (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z Fr q := by
    intro q Fr hF
    have hF' := hSpan hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨hgc, x, hx, hgx⟩ := hg
      exact gen x hx g ((mem_cusp _ _ _ _ _ _).1 hgc).1 hgx q
    | zero =>
      set_option synthInstance.maxHeartbeats 200000 in
      have e := geo_smul (O i) (u • cc) 1 0 0 q
      set_option synthInstance.maxHeartbeats 200000 in
      have e' := geo_smul (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z 0 0 q
      rw [zero_smul] at e e'
      rw [e, e']
      simp
    | add f g _ _ hf hg => rw [geo_add, geo_add, mul_add, mul_add, hf, hg]
    | smul a f _ hf => rw [geo_smul, geo_smul, mul_left_comm, hf, mul_left_comm]
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have rep : ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ q : AutQ (Wc D i),
      (O i).phi (u • cc) f q.out =
        D.what₂.embLL ζ' * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (actLev T.J.toCore.Q.c (O i).lev2 z f) q.out := by
    intro f hf q
    rw [hn] at hf
    have hfs : f ∈ sec _ _ (wtA (κ i)) (Vc D i).rank := ((mem_cusp _ _ _ _ _ _).1 hf).1
    have hF := ((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ (O i).hle _ (T.J.U ((i : ℕ) + 1)) _ _ _ hfs).2).2 hf
    have hBC := GlobalTheory.FieldBCModel.isBC_rulBC (O i).hle hfs.1
    have hs1 : ∀ k, ![f] k ∈ sec _ T.J.Q.c (wtA (κ i)) (Vc D i).rank := fun k => by
      rw [Subsingleton.elim k 0]; exact hfs
    have e := span q _ hF
    rw [geo_of_isBC (O i) hP.act.1 _ 1 (GlobalTheory.FieldBCModel.rulBC_mem_sec _ hfs) hs1 hBC q,
      geo_of_isBC (O i) hP.act.1 _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec _ hfs) hs1 hBC q] at e
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, map_one, OneMemClass.coe_one, one_mul] at e
    have h1 : actLev T.J.toCore.Q.c (O i).lev2 1 f = f :=
      actL_one _ _ _ hP.act.1.total hP.act.1.func hP.act.1.one hfs.1
    rw [h1] at e
    exact mul_left_cancel₀ hs0 (e.trans (by ring))
  have hcomp : ∀ γ ∈ GQ (Wc D i), ∀ g, ((O i).dict (γ * g)).1 = ((O i).dict g).1 := by
    obtain ⟨th, hr, -, hd⟩ := hT.j.dictU ((i : ℕ) + 1) (inR i) _ T.J.good_σ₀
    have key : ∀ (W : HSp D) (hV : T.J.V ((i : ℕ) + 1) T.J.σ₀ = W), ∀ γ ∈ GQ W, ∀ g,
        (castDict hV (T.J.dict ((i : ℕ) + 1) T.J.σ₀) (γ * g)).1 = (castDict hV (T.J.dict ((i : ℕ) + 1) T.J.σ₀) g).1 := by
      rintro W rfl γ hγ g
      obtain ⟨γ', -, he⟩ := hd.1 γ hγ g
      have e := congrArg Sigma.fst he
      exact e
    exact key _ (O i).hV
  have hsplit : ∀ (c' : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (f : T.J.R ((i : ℕ) + 1)) g,
      (O i).phi c' f g = c' ((O i).dict g).1 * (O i).phi (fun _ => 1) f g := by
    intro c' f g
    show c' _ * _ * _ = c' _ * (1 * _ * _)
    ring
  have hV : T.J.V ((i : ℕ) + 1) T.J.σ₀ = Wc D i := (O i).hV
  have hinv : ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ γ ∈ GQ (Wc D i), ∀ g,
      (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) f (γ * g) = (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) f g :=
    fun f hf => GlobalTheory.OneMapTuples.psi_inv T.J _ hV hT.j (inR i) (dom_wtA (κ i)) hf
  refine ⟨z, hz, ζ', m, hm, ?_, ?_⟩
  · apply D.what₂.embLL.injective
    rw [map_pow, map_one]
    exact hζm
  intro f hf g
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  have hzf := (hE z k hk f hf).1
  have hq : g * (⟦g⟧ : AutQ (Wc D i)).out⁻¹ ∈ GQ (Wc D i) :=
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel (GQ (Wc D i))) g)
  set γ := g * (⟦g⟧ : AutQ (Wc D i)).out⁻¹ with hγ
  have hg : g = γ * (⟦g⟧ : AutQ (Wc D i)).out := by rw [hγ, inv_mul_cancel_right]
  have hL : (O i).phi (u • cc) f g = (O i).phi (u • cc) f (⟦g⟧ : AutQ (Wc D i)).out := by
    have e := hinv f hf γ hq (⟦g⟧ : AutQ (Wc D i)).out
    rw [← hg] at e
    rw [hsplit (T.J.cE _ _) f g, hsplit (T.J.cE _ _) f, hg, hcomp γ hq] at e
    rw [← hg] at e
    have hne : T.J.cE ((i : ℕ) + 1) (O i).s0 ((O i).dict (⟦g⟧ : AutQ (Wc D i)).out).1 ≠ 0 :=
      norm_ne_zero_iff.1 ((hcU _).trans_ne one_ne_zero)
    have hc : ((O i).dict g).1 = ((O i).dict (⟦g⟧ : AutQ (Wc D i)).out).1 := by
      have := hcomp γ hq (⟦g⟧ : AutQ (Wc D i)).out
      rwa [← hg] at this
    rw [hsplit (u • cc) f g, hsplit (u • cc) f, hc, mul_left_cancel₀ hne e]
  rw [hL, rep f hf, ← hinv _ hzf γ hq, ← hg]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerPreservesVacuumConditionAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerPreservesVacuumConditionAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_eq {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_mul_transpose {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (ξ : A) (JA : Matrix α α A)
    (JB : Matrix β β A) (g : Matrix β β A) (hg : gᵀ * JB * g.map c = JB) (x : Matrix α β A) :
    symp c ξ JA JB (x * gᵀ) (x * gᵀ) = symp c ξ JA JB x x := by
  have e : (x * gᵀ) * JB * ((x * gᵀ).map c)ᵀ = x * JB * (x.map c)ᵀ := by
    have hm : (x * gᵀ).map c = x.map c * (gᵀ).map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    calc x * gᵀ * JB * (g.map c * (x.map c)ᵀ) = x * (gᵀ * JB * g.map c) * (x.map c)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq, hTens_eq, e]

variable {σ : E →ₐ[F] E}

theorem vecMulVec_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {x : Fin n → E} (hx : x ∈ X.L)
    {w : Fin d → AE F E} (hw : w ∈ latAt W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) w ∈ latAtV X W v := by
  let f : (Fin d → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun w => Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) w
      map_zero' := by ext i j; simp [Matrix.vecMulVec_apply]
      map_add' := fun w w' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add] }
  have : latAt W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    ext i j
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM,
      Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
    ring
  exact this hw

theorem mul_transpose_inv_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {h : UA σ W.J}
    (hh : h ∈ KAt σ W v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    γ * (mat h⁻¹)ᵀ ∈ latAtV X W v := by
  let f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => γ * (mat h⁻¹)ᵀ
      map_zero' := by simp
      map_add' := fun γ γ' => by simp [Matrix.add_mul] }
  have : latAtV X W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    show (a • incM F (Matrix.vecMulVec x y)) * (mat h⁻¹)ᵀ ∈ latAtV X W v
    have hz : (a • fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v :=
      AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, rfl⟩
    have e : (a • incM F (Matrix.vecMulVec x y)) * (mat h⁻¹)ᵀ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i))
          (mat h⁻¹ *ᵥ (a • fun i => inclR (F := F) (AF F) (y i))) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.mulVec,
        dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact vecMulVec_mem_latAtV X W v hx (hh.2 _ hz).2
  exact this hγ

end GlobalTheory.InertSph

namespace GlobalTheory.InertSph

theorem acts_vacCond_of_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, k)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v θ hθ k hk φ hφ φ₁ hφ₁ hAct hvac γ hγ r hr
  have hS := IsUWeilPair.isUSplitting hTr.weil'
  have etens : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [smul_zero, e0]
    funext x
    simp [Darboux.rho, schr]
  have hrφ : Rest (evFin F v) φ r := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v φ₁ φ r h0 hφ hr
  set γ' := actAB (cA σ) ((1 : UA σ G.V'.J), k⁻¹) γ
  have eγ' : γ' = γ * (mat k⁻¹)ᵀ := by
    simp [γ', actAB, mat]
  have hγ' : γ' ∈ latAtV G.V' G.W v := by
    rw [eγ']; exact mul_transpose_inv_mem_latAtV G.V' G.W v hk hγ
  have hsym : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ' γ' =
      symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ := by
    rw [eγ']
    exact symp_mul_transpose (cA σ) _ _ _ (mat k⁻¹) (k⁻¹).2 γ
  have e1 : actAB (cA σ) ((1 : UA σ G.V'.J), k) γ' = γ := by
    simp only [γ', actAB]
    simp [Matrix.mul_assoc, ← Matrix.transpose_mul]
  have hi := hS.impl ((1 : UA σ G.V'.J), k) γ' _ hrφ.2
  rw [e1] at hi
  rw [← hAct r hrφ, ← hi, hvac γ' hγ' r hrφ, hsym, etens, map_smul, hAct r hrφ, etens]

end GlobalTheory.InertSph
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerPreservesVacuumConditionAtPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryStabilizer_preserves_vacuumCondition_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, k)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | exact GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | (intros; apply GlobalTheory.InertSph.acts_vacCond_of_mem_KAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinear
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SurjAtPlaceV

open GlobalTheory.LeviAtPlace

theorem surj_at_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)), ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t g'
  have h := hTr.base.cm
  have hJ : IsUnit (G.V.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hV.sig (InfinitePlace.mk φ))
    have h1 : G.V.J.det ≠ 0 := fun e => h0 (by
      rw [show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨leviHom h t G.V.J hJ hTr.geo.hV.herm g', lift_sub_one_at v _, ?_⟩
  rw [leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, pairMat_fst]

end GlobalTheory.SurjAtPlaceV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_group_surjects_general_linear : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)), ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  first | exact @GlobalTheory.SurjAtPlaceV.surj_at_place | exact GlobalTheory.SurjAtPlaceV.surj_at_place | (intros; apply GlobalTheory.SurjAtPlaceV.surj_at_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupIdempotentCoefficients
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

noncomputable section

namespace GlobalTheory.TieIdem

theorem coeff_conj_of_central' {K : Type} [Field K] {G : Type} [Group G] (e : MonoidAlgebra K G)
    (he : ∀ x, x * e = e * x) (k g : G) : e.coeff (k * g * k⁻¹) = e.coeff g := by
  have h := congrArg (fun a : MonoidAlgebra K G => a.coeff (k * g)) (he (MonoidAlgebra.single k 1))
  simp only [MonoidAlgebra.mul_single_apply, MonoidAlgebra.single_mul_apply] at h
  simpa [mul_assoc] using h.symm

theorem idemOf_props {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    (∀ k : G, ∑ g, (idemOf X).coeff g * (idemOf X).coeff (g⁻¹ * k) = (idemOf X).coeff k) ∧
    (∀ g h : G, (idemOf X).coeff (h * g * h⁻¹) = (idemOf X).coeff g) ∧
    (∀ g : G, IsIntegral ℤ ((Fintype.card G : K) * (idemOf X).coeff g)) ∧
    ∀ (σ : K →+* ℂ) (g : G), σ ((idemOf X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf X).coeff g)) := by
  refine ⟨fun k => ?_, fun g h => ?_, fun g => ?_, fun σ g => ?_⟩
  · rw [← coeff_mul_fin, idemOf_mul_self X hX]
  · exact coeff_conj_of_central' _ (fun b => idemOf_central X hX b) h g
  · obtain ⟨b, hb⟩ := idemOf_integral X hX g
    rw [← hb]
    exact b.isIntegral_coe
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      have h1 := (hX χ hχ).map_inv σ 1
      have h2 := (hX χ hχ).map_inv σ g
      rw [inv_one] at h1
      simp only [map_mul, map_div₀, map_natCast, inv_inv, h2, Complex.conj_conj]
      rw [← h1]

end GlobalTheory.TieIdem

namespace GlobalTheory.TieIdem

end GlobalTheory.TieIdem
end
end
