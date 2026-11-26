module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

def chartHom (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : Γ(PSpace ℤ N, chart ℤ N c) →+* ℂ :=
  (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : {j // j ≠ c} => w j.1 / w c)).comp
    (chartAlgEquiv ℤ N c).symm.toRingEquiv.toRingHom

def ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : CxPts (PSpace.str ℤ N) σ₀ :=
  CxPts.ofHom (isAffineOpen_chart ℤ N c) (chartHom N c w)
    (fun a => RingHom.congr_fun (RingHom.ext_int ((chartHom N c w).comp (DVR.FlatBC.algX _ _)) σ₀) a)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def multiprojectivePoint (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) : CxPts (mpStr ℤ m n) σ₀ :=
  ⟨GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (spMap σ₀)
      (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).1) (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).2),
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift_mpStr _ _ _ _ _⟩

theorem map_prB_ptMP (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) :
    (GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ (multiprojectivePoint c z)) =
      ptP (n k) (c k) (fun i => z ⟨k, i⟩) :=
  Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ k)

end GlobalTheory.CompanionTheory.MPSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectiveChartHolomorphicCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnEvProd
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.Ar.ProdHolo

variable {k : Type} [CommRing k] {Z X : Scheme.{0}} {q : Z ⟶ Sp k} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem mem_ptsIn_preimage {π : Z ⟶ X} {z : CxPts q σ} {x : CxPts p σ} (h : z.1 ≫ π = x.1)
    {U : X.Opens} (hx : x ∈ ptsIn p σ U) : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := by
  rw [mem_ptsIn] at hx ⊢
  rw [← h] at hx
  exact hx

theorem ev_appLE {π : Z ⟶ X} {z : CxPts q σ} {x : CxPts p σ} (h : z.1 ≫ π = x.1)
    {U : X.Opens} {W : Z.Opens} (e : W ≤ π ⁻¹ᵁ U) (hz : z ∈ ptsIn q σ W)
    (a : Γ(X, U)) :
    CxPts.ev q σ W ((π.appLE U W e).hom a) z = CxPts.ev p σ U a x := by
  have h1 := GlobalTheory.CxPts.ev_res (p := q) (σ := σ) e hz ((π.app U).hom a)
  refine Eq.trans ?_ (h1.trans ?_)
  · rfl
  · have h2 := GlobalTheory.Points.valR_comp z.1 π U a
    rw [h] at h2
    exact h2.symm

theorem differentiableOn_ev_prod : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (σ : k →+* ℂ) {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] (T : Set E) (U : X.Opens) (V : Y.Opens), IsAffineOpen U → IsAffineOpen V →
  ∀ (s₁ : E → CxPts f σ) (s₂ : E → CxPts g σ) (s : E → CxPts (pullback.fst f g ≫ f) σ),
  (∀ v, (s v).1 ≫ pullback.fst f g = (s₁ v).1) → (∀ v, (s v).1 ≫ pullback.snd f g = (s₂ v).1) →
  (∀ v ∈ T, s₁ v ∈ ptsIn f σ U) → (∀ v ∈ T, s₂ v ∈ ptsIn g σ V) →
  (∀ a : Γ(X, U), DifferentiableOn ℂ (CxPts.ev f σ U a ∘ s₁) T) →
  (∀ b : Γ(Y, V), DifferentiableOn ℂ (CxPts.ev g σ V b ∘ s₂) T) →
  IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ∧
  (∀ v ∈ T, s v ∈ ptsIn (pullback.fst f g ≫ f) σ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) ∧
  ∀ t : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V),
    DifferentiableOn ℂ (CxPts.ev (pullback.fst f g ≫ f) σ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) t ∘ s) T := by
  intro k _ X Y f g σ E _ _ T U V hU hV s₁ s₂ s h₁ h₂ m₁ m₂ d₁ d₂
  have H := IsPullback.of_hasPullback f g
  obtain ⟨hW, po⟩ := GlobalTheory.Conormal.isAffineOpen_and_isPushout H (U := ⊤) (T₀ := V) (W := U)
    (isAffineOpen_top _) hV hU le_top le_top
  have hin : ∀ v ∈ T, s v ∈ ptsIn (pullback.fst f g ≫ f) σ
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := fun v hv =>
    mem_ptsIn_inf.2 ⟨mem_ptsIn_preimage (h₁ v) (m₁ v hv), mem_ptsIn_preimage (h₂ v) (m₂ v hv)⟩
  refine ⟨hW, hin, fun t => ?_⟩
  have ht : t ∈ Subring.closure (Set.range (pullback.fst f g |>.appLE U
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_left).hom ∪
      Set.range (pullback.snd f g |>.appLE V
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_right).hom) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout po]
    trivial
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact (d₁ a).congr fun v hv => ev_appLE (h₁ v) _ (hin v hv) a
    · exact (d₂ b).congr fun v hv => ev_appLE (h₂ v) _ (hin v hv) b
  | zero =>
    exact (differentiableOn_const 0).congr fun v hv => by
      simp only [Function.comp_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_zero]
  | one =>
    exact (differentiableOn_const 1).congr fun v hv => by
      simp only [Function.comp_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_one]
  | add x y _ _ hx hy =>
    exact (hx.add hy).congr fun v hv => by
      simp only [Function.comp_apply, Pi.add_apply, GlobalTheory.CxPts.ev_add]
  | neg x _ hx =>
    exact hx.neg.congr fun v hv => by
      simp only [Function.comp_apply, Pi.neg_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_neg]
  | mul x y _ _ hx hy =>
    exact (hx.mul hy).congr fun v hv => by
      simp only [Function.comp_apply, Pi.mul_apply, GlobalTheory.CxPts.ev_mul]

end GlobalTheory.CompanionTheory.Ar.ProdHolo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnEvPtP
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem differentiableOn_eval₂_ratio (N : ℕ) (c : Fin (N + 1))
    (p : MvPolynomial {j : Fin (N + 1) // j ≠ c} ℤ) :
    DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ =>
      MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : {j // j ≠ c} => w j.1 / w c) p)
      {w | w c ≠ 0} := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact differentiableOn_const _
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at hp ⊢
    have hj : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => w j.1) {w | w c ≠ 0} :=
      (differentiable_apply j.1).differentiableOn
    have hc : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => w c) {w | w c ≠ 0} :=
      (differentiable_apply c).differentiableOn
    have hinv : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => (w c)⁻¹) {w | w c ≠ 0} :=
      fun w hw => (hc w hw).inv hw
    simp only [div_eq_mul_inv]
    exact hp.mul (hj.mul hinv)

theorem differentiableOn_ev_ptP (N : ℕ) (c : Fin (N + 1)) (a : Γ(PSpace ℤ N, chart ℤ N c)) :
    DifferentiableOn ℂ (fun w => CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w))
      {w | w c ≠ 0} := by
  have h : (fun w => CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w)) =
      fun w : Fin (N + 1) → ℂ => MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun j : {j // j ≠ c} => w j.1 / w c) ((chartAlgEquiv ℤ N c).symm a) := by
    funext w
    exact CxPts.ev_ofHom _ _ _ a
  rw [h]
  exact differentiableOn_eval₂_ratio N c _

end GlobalTheory.CompanionTheory.MPSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectiveChartHolomorphicCoordinates
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem mchart_zero (n : Fin 1 → ℕ) (c : ∀ k, Bk n k) :
    mchart c = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) := by
  apply TopologicalSpace.Opens.ext
  ext x
  refine ⟨fun hx => Set.mem_iInter.1 hx 0, fun hx => Set.mem_iInter.2 fun k => ?_⟩
  obtain rfl : k = 0 := Fin.fin_one_eq_zero k
  exact hx

theorem mchart_succ {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) :
    mchart c = (pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
      pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
        mchart (n := Fin.tail n) (fun j => c j.succ) : (MP ℤ (m + 1) n).Opens) := by
  apply TopologicalSpace.Opens.ext
  ext x
  refine ⟨fun hx => ⟨Set.mem_iInter.1 hx 0, Set.mem_iInter.2 fun j => Set.mem_iInter.1 hx j.succ⟩,
    fun hx => Set.mem_iInter.2 fun k => ?_⟩
  induction k using Fin.cases with
  | zero => exact hx.1
  | succ j => exact Set.mem_iInter.1 hx.2 j

theorem multiprojectivePoint_fst {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (multiprojectivePoint c z).1 ≫ pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) =
      (ptP (n 0) (c 0) (fun i => z ⟨0, i⟩)).1 :=
  GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ 0

theorem multiprojectivePoint_snd {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (multiprojectivePoint c z).1 ≫ pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) =
      (multiprojectivePoint (n := Fin.tail n) (fun j => c j.succ) (fun p => z ⟨p.1.succ, p.2⟩)).1 :=
  pullback.lift_snd _ _ _

theorem multiprojective_chart_affine_holomorphic_points (m : ℕ) : ∀ (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
    (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c)) ∧
    ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ multiprojectivePoint c)
      {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  induction m with
  | zero =>
    intro n c
    have key : ∀ W : (MP ℤ 0 n).Opens, W = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) → IsAffineOpen W ∧
        (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ 0 n) σ₀ W) ∧
        ∀ a : Γ(MP ℤ 0 n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ 0 n) σ₀ W a ∘ multiprojectivePoint c)
          {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      rintro W rfl
      have hpt : ∀ z : (Σ k, Bk n k) → ℂ, multiprojectivePoint c z = ptP (n 0) (c 0) (fun i => z ⟨0, i⟩) := fun z => rfl
      refine ⟨isAffineOpen_chart ℤ (n 0) (c 0), fun z _ => ?_, fun a => ?_⟩
      · rw [hpt]
        exact CxPts.ofHom_mem _ _ _
      · have hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩) :=
          differentiable_pi.2 fun i => differentiable_apply _
        exact (GlobalTheory.CompanionTheory.MPSmooth.differentiableOn_ev_ptP (n 0) (c 0) a).comp hL.differentiableOn fun z hz => hz 0
    exact key _ (mchart_zero n c)
  | succ m ih =>
    intro n c
    obtain ⟨hA, hM, hD⟩ := ih (Fin.tail n) (fun j => c j.succ)
    have hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩) :=
      differentiable_pi.2 fun p => differentiable_apply _
    have hL0 : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩) :=
      differentiable_pi.2 fun i => differentiable_apply _
    have hT : Set.MapsTo (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩)
        {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
        {z : (Σ k, Bk (Fin.tail n) k) → ℂ | ∀ k, z ⟨k, c k.succ⟩ ≠ 0} := fun z hz k => hz k.succ
    have main := GlobalTheory.CompanionTheory.Ar.ProdHolo.differentiableOn_ev_prod (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) σ₀
      {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} (chart ℤ (n 0) (c 0))
      (mchart (n := Fin.tail n) (fun j => c j.succ))
      (isAffineOpen_chart ℤ (n 0) (c 0)) hA
      (fun z => ptP (n 0) (c 0) (fun i => z ⟨0, i⟩))
      (fun z => multiprojectivePoint (n := Fin.tail n) (fun j => c j.succ) (fun p => z ⟨p.1.succ, p.2⟩))
      (multiprojectivePoint c) (multiprojectivePoint_fst n c) (multiprojectivePoint_snd n c)
      (fun z _ => CxPts.ofHom_mem _ _ _) (fun z hz => hM _ (hT hz))
      (fun a => (GlobalTheory.CompanionTheory.MPSmooth.differentiableOn_ev_ptP (n 0) (c 0) a).comp hL0.differentiableOn fun z hz => hz 0)
      (fun b => (hD b).comp hL.differentiableOn hT)
    have key : ∀ W : (MP ℤ (m + 1) n).Opens,
        W = (pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
          pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
            mchart (n := Fin.tail n) (fun j => c j.succ) : (MP ℤ (m + 1) n).Opens) → IsAffineOpen W ∧
        (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ (m + 1) n) σ₀ W) ∧
        ∀ a : Γ(MP ℤ (m + 1) n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ (m + 1) n) σ₀ W a ∘ multiprojectivePoint c)
          {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      rintro W rfl
      exact main
    exact key _ (mchart_succ n c)

theorem mchart_affine_holo : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
    ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c)
      {z | ∀ k, z ⟨k, c k⟩ ≠ 0} :=
  fun m n c => ⟨(multiprojective_chart_affine_holomorphic_points m n c).1, (multiprojective_chart_affine_holomorphic_points m n c).2.2⟩

end GlobalTheory.CompanionTheory.MPSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectiveChartHolomorphicCoordinatesStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiprojective_chart_holomorphic_coordinates : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
  ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c)
    {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo | exact GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePointOfNonvanishingCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectivePointChartRatio
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectivePointChartRatio
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem ptP_mem_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c) :=
  CxPts.ofHom_mem _ _ _

theorem ev_ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (a : Γ(PSpace ℤ N, chart ℤ N c)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w) = chartHom N c w a :=
  CxPts.ev_ofHom _ _ _ a

theorem ev_ptP_ratio (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) (ratio ℤ N c i) (ptP N c w) = w i / w c := by
  rw [ev_ptP]
  by_cases h : i = c
  · subst h
    rw [ratio, ratioOn_self, map_one, div_self hc]
  · have e : (chartAlgEquiv ℤ N c).symm (ratio ℤ N c i) = X ⟨i, h⟩ := by
      rw [← chartAlgEquiv_X ℤ N c ⟨i, h⟩]
      exact AlgEquiv.symm_apply_apply _ _
    simp [chartHom, e]

theorem ptP_mem_chart_iff (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0 := by
  have e := CxPts.mem_ptsIn_basicOpen (ptP_mem_chart N c w) (ratio ℤ N c i)
  rw [ratio, basicOpen_ratioOn, CxPts.mem_ptsIn_inf] at e
  rw [← ratio, ev_ptP_ratio N c w hc i] at e
  constructor
  · intro h
    have := e.1 ⟨ptP_mem_chart N c w, h⟩
    exact fun h0 => this (by rw [h0, zero_div])
  · intro h
    exact (e.2 (div_ne_zero h hc)).2

theorem ptP_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0) :
    (∀ i, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0) ∧
    ∀ i j, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) →
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (GlobalTheory.CompanionTheory.MPSmooth.ptP N c w) =
        w j / w i := by
  refine ⟨ptP_mem_chart_iff N c w hc, fun i j hi => ?_⟩
  have hwi : w i ≠ 0 := (ptP_mem_chart_iff N c w hc i).1 hi
  have hW : ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i) :=
    CxPts.mem_ptsIn_inf.2 ⟨ptP_mem_chart N c w, hi⟩
  have h₁ : ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left i *
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j =
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left j :=
    ratioOn_mul_ratioOn
  have h₂ := congrArg (fun f => CxPts.ev (PSpace.str ℤ N) σ₀ _ f (ptP N c w)) h₁
  simp only [CxPts.ev_mul] at h₂
  have ea : ∀ k, CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left k) (ptP N c w) = w k / w c := fun k =>
    (CxPts.ev_res inf_le_left hW (ratio ℤ N c k)).trans (ev_ptP_ratio N c w hc k)
  have eb : CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j) (ptP N c w) =
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (ptP N c w) :=
    CxPts.ev_res inf_le_right hW (ratio ℤ N i j)
  rw [ea, ea, eb] at h₂
  field_simp at h₂ ⊢
  exact h₂

end GlobalTheory.CompanionTheory.MPSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectivePointChartRatioStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_point_chart_ratio : ∀ (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ), w c ≠ 0 →
  (∀ i, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0) ∧
  ∀ i j, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) →
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (GlobalTheory.CompanionTheory.MPSmooth.ptP N c w) = w j / w i := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.ptP_chart | exact GlobalTheory.CompanionTheory.MPSmooth.ptP_chart | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.ptP_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePointOfNonvanishingCoords
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem mem_blockChart_iff (y : CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) (i : Bk n k) :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔
      GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ y ∈
        ptsIn (PSpace.str ℤ (n k)) σ₀ (chart ℤ (n k) i) :=
  Iff.rfl

theorem ev_pullRatio (y : CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) (i j : Bk n k) :
    CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y =
      CxPts.ev (PSpace.str ℤ (n k)) σ₀ (chart ℤ (n k) i) (ratio ℤ (n k) i j)
        (GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ y) := by
  have e : pullRatio (prB n k) (blockChart n k i) i le_rfl j = (prB n k).app (chart ℤ (n k) i) (ratio ℤ (n k) i j) := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  rw [e]
  exact CxPts.ev_app (p := PSpace.str ℤ (n k)) (q := mpStr ℤ m n) (prB n k)
    (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) y

theorem isUnder_ptMP (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    IsUnder (GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z) z ∧ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  have H : IsUnder (multiprojectivePoint c z) z := fun k i => by
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.projective_point_chart_ratio (n k) (c k) (fun i => z ⟨k, i⟩) (hz k)
    have e := map_prB_ptMP c z k
    refine ⟨?_, fun j hy => ?_⟩
    · rw [mem_blockChart_iff, e]
      exact h₁ i
    · rw [ev_pullRatio, e]
      exact h₂ i j (by rw [← e]; exact (mem_blockChart_iff _ k i).1 hy)
  refine ⟨H, CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => ?_)⟩
  exact CxPts.mem_ptsIn.1 ((H k (c k)).1.2 (hz k))

end GlobalTheory.CompanionTheory.MPSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePointOfNonvanishingCoordsStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiprojective_point_of_nonvanishing_coords : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ), (∀ k, z ⟨k, c k⟩ ≠ 0) →
  IsUnder (GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z) z ∧ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.isUnder_ptMP | exact GlobalTheory.CompanionTheory.MPSmooth.isUnder_ptMP | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.isUnder_ptMP <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSectionSmoothComposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSectionSmoothComposition
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.CxSmooth

private theorem analyticAt_of_differentiableOn_open {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h U) {c : Fin n → ℂ} (hc : c ∈ U) :
    AnalyticAt ℂ h c := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hc)
  have hd : ∀ ζ ∈ Metric.closedBall c r, DifferentiableAt ℂ h ζ :=
    fun ζ hζ => hh.differentiableAt (hU.mem_nhds (hrU hζ))
  have hA : AnalyticAt ℂ (fun w => ((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ *
      ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd (ReciprocityTheory.AnForm.Osgood.kern c r w)) c :=
    analyticAt_const.mul
      (((ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd).analyticAt _).comp
        (ReciprocityTheory.AnForm.Osgood.kern_analyticAt c hr))
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ^ n ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero)
  refine hA.congr ?_
  filter_upwards [Metric.ball_mem_nhds c hr] with w hw
  rw [ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hr hd hw]
  exact inv_mul_cancel_left₀ h2 (h w)

theorem analyticAt_of_differentiableOn {ι : Type} [Fintype ι] {U : Set (ι → ℂ)} (hU : IsOpen U)
    {f : (ι → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {z : ι → ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z := by
  classical
  let e := Fintype.equivFin ι
  let φ : (Fin (Fintype.card ι) → ℂ) →L[ℂ] (ι → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e)
  let ψ : (ι → ℂ) →L[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e.symm)
  have hφψ : ∀ w, φ (ψ w) = w := fun w => funext fun i => by simp [φ, ψ]
  have hmem : ψ z ∈ φ ⁻¹' U := by
    rw [Set.mem_preimage, hφψ]
    exact hz
  have hA := analyticAt_of_differentiableOn_open (hU.preimage φ.continuous)
    (hf.comp φ.differentiableOn (Set.mapsTo_preimage φ U)) hmem
  have hB := hA.comp (ψ.analyticAt z)
  have heq : (f ∘ ⇑φ) ∘ ⇑ψ = f := funext fun w => by simp only [Function.comp_apply, hφψ]
  rwa [heq] at hB

theorem contDiffAt_comp_of_cInfAt : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {ι : Type} [Fintype ι]
  {T : Set (ι → ℂ)} {s : (ι → ℂ) → CxPts p σ} {f : CxPts p σ → ℝ} {z₀ : ι → ℂ}, IsOpen T → ContinuousOn s T →
  (∀ (W : Y.Opens) (g : Γ(Y, W)), DifferentiableOn ℂ (CxPts.ev p σ W g ∘ s) (T ∩ s ⁻¹' ptsIn p σ W)) →
  z₀ ∈ T → CInfAt f (s z₀) → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ s) z₀ := by
  intro k _ Y p σ ι _ T s f z₀ hT hs hd hz h
  obtain ⟨W, ι', _, g, F, O, hyW, hO, hmem, hF, hev⟩ := h
  have hN : IsOpen (T ∩ s ⁻¹' ptsIn p σ W) := hs.isOpen_inter_preimage hT (isOpen_ptsIn W)
  have hzN : z₀ ∈ T ∩ s ⁻¹' ptsIn p σ W := ⟨hz, hyW⟩
  have hG : AnalyticAt ℂ (fun z a => ev p σ W (g a) (s z)) z₀ :=
    analyticAt_pi_iff.2 fun a => analyticAt_of_differentiableOn hN (hd W (g a)) hzN
  have hcont : ContinuousAt s z₀ := hs.continuousAt (hT.mem_nhds hz)
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F ∘ fun z a => ev p σ W (g a) (s z)) z₀ :=
    (hF.contDiffAt (hO.mem_nhds hmem)).comp z₀ (hG.contDiffAt.restrict_scalars ℝ)
  exact h1.congr_of_eventuallyEq (hev.comp_tendsto hcont)

end GlobalTheory.CompanionTheory.CxSmooth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSectionSmoothCompositionStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_section_smooth_composition : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {ι : Type} [Fintype ι]
  {T : Set (ι → ℂ)} {s : (ι → ℂ) → CxPts p σ} {f : CxPts p σ → ℝ} {z₀ : ι → ℂ}, IsOpen T → ContinuousOn s T →
  (∀ (W : Y.Opens) (g : Γ(Y, W)), DifferentiableOn ℂ (CxPts.ev p σ W g ∘ s) (T ∩ s ⁻¹' ptsIn p σ W)) →
  z₀ ∈ T → CInfAt f (s z₀) → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ s) z₀ := by
  first | exact @GlobalTheory.CompanionTheory.CxSmooth.contDiffAt_comp_of_cInfAt | exact GlobalTheory.CompanionTheory.CxSmooth.contDiffAt_comp_of_cInfAt | (intros; apply GlobalTheory.CompanionTheory.CxSmooth.contDiffAt_comp_of_cInfAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmooth
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem smooth_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → Geo.IsSmoothHerm A := by
  rintro m n M A ⟨u, -, -, hA⟩ z₀ hz₀
  choose c hc using hz₀
  refine ContDiffAt.contDiffWithinAt ?_
  let T : Set ((Σ k, Bk n k) → ℂ) := {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
  have hT : IsOpen T := by
    have : T = ⋂ k, {z : (Σ k, Bk n k) → ℂ | z ⟨k, c k⟩ ≠ 0} := by ext; simp [T]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
  have hz : z₀ ∈ T := hc
  let s := multiprojectivePoint (m := m) (n := n) c
  obtain ⟨haff, hgen⟩ := GlobalTheory.T.multiprojective_chart_holomorphic_coordinates m n c
  have hmem : ∀ z ∈ T, s z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := fun z h => (GlobalTheory.T.multiprojective_point_of_nonvanishing_coords m n c z h).2
  obtain ⟨hcont, hholo⟩ := holo_of_affine haff hT hmem hgen
  obtain ⟨i, hi⟩ := exists_mem_ptsIn M.isLB.cover (s z₀)
  have hV : s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) := mem_ptsIn_inf.2 ⟨hi, hmem z₀ hz⟩

  let F : CxPts (mpStr ℤ m n) σ₀ → ℝ := fun y =>
    ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
      Real.exp ((M.φ σ₀).φ i y / 2)
  have hF : CInfAt F (s z₀) := by
    have h1 : CInfAt (fun y => ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)
        (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖) (s z₀) := by
      refine ⟨M.B.U i ⊓ mchart c, Unit, inferInstance, fun _ => (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)),
        fun v => ‖v ()‖, {v | v () ≠ 0}, hV, isOpen_ne_fun (continuous_apply _) continuous_const,
        ev_ne_zero hV (u i c).isUnit, ?_, Filter.EventuallyEq.rfl⟩
      intro v hv
      exact ((contDiffAt_norm ℝ hv).comp v ((contDiff_apply ℝ (fun _ => ℂ) ()).contDiffAt)).contDiffWithinAt
    have h2 := (M.cInf σ₀) i (s z₀) hi
    exact h1.comp₂ h2 (G := fun x => x.1 * Real.exp (x.2 / 2))
      (contDiff_fst.mul (Real.contDiff_exp.comp (contDiff_snd.div_const 2)))
  have hFs := GlobalTheory.T.holomorphic_section_smooth_composition hT hcont hholo hz hF
  have hP : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) z₀ := by
    refine contDiffAt_prod fun k _ => ?_
    have hn : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ‖z ⟨k, c k⟩‖) z₀ :=
      (contDiffAt_norm ℝ (hc k)).comp z₀ ((contDiff_apply ℝ (fun _ => ℂ) (⟨k, c k⟩ : Σ k, Bk n k)).contDiffAt)
    have hx : ‖z₀ ⟨k, c k⟩‖ ≠ 0 := norm_ne_zero_iff.2 (hc k)
    cases h : A.a k with
    | ofNat j =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast]
      exact hn.pow j
    | negSucc j =>
      simp only [zpow_negSucc]
      exact (hn.pow (j + 1)).inv (pow_ne_zero _ hx)
  refine (hP.mul hFs).congr_of_eventuallyEq ?_
  have hnb : ∀ᶠ z in nhds z₀, z ∈ T ∧ s z ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) :=
    Filter.Eventually.and (hT.mem_nhds hz) ((hcont.continuousAt (hT.mem_nhds hz)).preimage_mem_nhds ((isOpen_ptsIn _).mem_nhds hV))
  filter_upwards [hnb] with z hz'
  rw [hA i c (s z) z (GlobalTheory.T.multiprojective_point_of_nonvanishing_coords m n c z hz'.1).1 hz'.2]
  simp only [F, Function.comp_apply]
  ring

end GlobalTheory.CompanionTheory.MPSmooth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmoothStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_line_bundle_smooth : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → Geo.IsSmoothHerm A := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep | exact GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep <;> assumption)
end
