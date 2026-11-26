module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ]

instance : SemilatticeSup {I : Finset κ // I.Nonempty} :=
  Subtype.semilatticeSup fun _ _ hx _ => hx.mono Finset.subset_union_left

abbrev NE (κ : Type) [LinearOrder κ] : Type := ({I : Finset κ // I.Nonempty})ᵒᵈ

abbrev ne (s : Finset κ) (h : s.Nonempty) : (NE κ)ᵒᵖ := op (OrderDual.toDual ⟨s, h⟩)

abbrev sub (a : (NE κ)ᵒᵖ) : Finset κ := (OrderDual.ofDual a.unop).1

theorem sub_nonempty (a : (NE κ)ᵒᵖ) : (sub a).Nonempty := (OrderDual.ofDual a.unop).2

theorem sub_subset {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) : sub a ⊆ sub b := leOfHom f.unop

def homOf {a b : (NE κ)ᵒᵖ} (h : sub a ⊆ sub b) : a ⟶ b := (homOfLE (show b.unop ≤ a.unop from h)).op

def mn (a : (NE κ)ᵒᵖ) : κ := (sub a).min' (sub_nonempty a)

theorem mn_mem (a : (NE κ)ᵒᵖ) : mn a ∈ sub a := Finset.min'_mem _ _

theorem mn_le_of_hom {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) : mn b ≤ mn a :=
  Finset.min'_le _ _ (sub_subset f (mn_mem a))

theorem card_nonempty {p : ℕ} (s : {s : Finset κ // s.card = p + 1}) : s.1.Nonempty :=
  Finset.card_pos.1 (by rw [s.2]; omega)

theorem card_three {x y z : κ} (h₁ : x < y) (h₂ : y < z) : ({x, y, z} : Finset κ).card = 2 + 1 := by
  rw [Finset.card_insert_of_notMem (by simp [h₁.ne, (h₁.trans h₂).ne]), Finset.card_pair h₂.ne]

section Cech

variable {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

abbrev CC (p : ℕ) : Type := ∀ s : {s : Finset κ // s.card = p + 1}, F.obj (ne s.1 (card_nonempty s))

def δ (p : ℕ) : CC F p →ₗ[R] CC F (p + 1) :=
  LinearMap.pi fun t => ∑ i : t.1, GlobalTheory.cubeSign t.1 i.1 •
    ((mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t i))) (b := ne _ (card_nonempty t))
      (Finset.erase_subset i.1 t.1))).toLinearMap ∘ₗ LinearMap.proj (GlobalTheory.Cube.eraseIdx t i))

theorem δ_apply (p : ℕ) (x : CC F p) (t : {s : Finset κ // s.card = p + 1 + 1}) :
    δ F p x t = ∑ i : t.1, GlobalTheory.cubeSign t.1 i.1 •
      mp F (homOf (a := ne _ (card_nonempty (GlobalTheory.Cube.eraseIdx t i))) (b := ne _ (card_nonempty t))
        (Finset.erase_subset i.1 t.1)) (x (GlobalTheory.Cube.eraseIdx t i)) := by
  simp [δ, LinearMap.sum_apply]

def e0 : CC F 0 →ₗ[R] C0 F :=
  LinearMap.pi fun a => (mp F (homOf (a := ne {mn a} (Finset.singleton_nonempty _)) (b := a)
    (Finset.singleton_subset_iff.2 (mn_mem a)))).toLinearMap ∘ₗ
      LinearMap.proj (⟨{mn a}, Finset.card_singleton _⟩ : {s : Finset κ // s.card = 0 + 1})

theorem pair_subset {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) : ({mn b, mn a} : Finset κ) ⊆ sub b := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact mn_mem b
  · exact sub_subset f (mn_mem a)

theorem triple_subset {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    ({mn d, mn b, mn a} : Finset κ) ⊆ sub d := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact mn_mem d
  · exact sub_subset g (mn_mem b)
  · exact sub_subset g (sub_subset f (mn_mem a))

def e1 : CC F 1 →ₗ[R] C1 F :=
  LinearMap.pi fun a => LinearMap.pi fun b => LinearMap.pi fun f =>
    if h : mn b < mn a then
      -((mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b) (pair_subset f))).toLinearMap ∘ₗ
        LinearMap.proj (⟨{mn b, mn a}, Finset.card_pair h.ne⟩ : {s : Finset κ // s.card = 1 + 1}))
    else 0

def e2 : CC F 2 →ₗ[R] C2 F :=
  LinearMap.pi fun a => LinearMap.pi fun b => LinearMap.pi fun d => LinearMap.pi fun f =>
    LinearMap.pi fun g =>
    if h : mn d < mn b ∧ mn b < mn a then
      -((mp F (homOf (a := ne {mn d, mn b, mn a} (Finset.insert_nonempty _ _)) (b := d)
          (triple_subset f g))).toLinearMap ∘ₗ
        LinearMap.proj (⟨{mn d, mn b, mn a}, card_three h.1 h.2⟩ : {s : Finset κ // s.card = 2 + 1}))
    else 0

end Cech

section Scheme

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def cov (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (I : NE κ) :
    X.affineOpens :=
  ⟨⨅ i ∈ (OrderDual.ofDual I).1, D i, hD _ (OrderDual.ofDual I).2⟩

theorem cov_mono (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    Monotone (cov D hD) := fun _ _ h => show (⨅ i ∈ _, D i) ≤ ⨅ i ∈ _, D i from biInf_mono fun _ hi => h hi

abbrev covF (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R :=
  (cov_mono D hD).functor.op ⋙ OAff s

def res0 (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    LinearMap.ker (d0 (OAff s)) →ₗ[R] LinearMap.ker (d0 (covF s D hD)) where
  toFun g := ⟨fun I => g.1 (op (cov D hD I.unop)), by
    funext I J f
    exact congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) _) _) ((cov_mono D hD).functor.map f.unop).op⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem triv_pull_U {X' : Scheme.{0}} (φ : X' ⟶ X) (j : ((LB.triv X).pull φ).ι) :
    ((LB.triv X).pull φ).U j = ⊤ := by
  ext x; simp [LB.pull, LB.LinComb, LB.wchart]

def i0 {X' : Scheme.{0}} (φ : X' ⟶ X) : ((LB.triv X).pull φ).ι := fun _ => PUnit.unit

def trivCoord {X' : Scheme.{0}} {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (V : X'.Opens) :
    GlobalTheory.AbLaw.SecOnR s' ((LB.triv X).pull φ) V →ₗ[R'] Sec s' V where
  toFun x := Sec.res s' (le_inf le_rfl (by rw [triv_pull_U]; exact le_top)) (GlobalTheory.AbLaw.SecOnR.coord x (i0 φ))
  map_add' x y := by simp [GlobalTheory.AbLaw.SecOnR.coord_add]; exact map_add _ _ _
  map_smul' r x := by
    have e : (show Sec s' _ from (r • x).coord (i0 φ)) = r • (show Sec s' _ from x.coord (i0 φ)) := by
      rw [GlobalTheory.AbLaw.SecOnR.coord_base_smul]; rfl
    exact (congrArg (Sec.res s' _) e).trans (map_smul _ _ _)

def Φ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
    {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) (D : κ → X.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) :
    R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p →ₗ[R'] CC (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p :=
  (LinearMap.pi fun t => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) ∘ₗ LinearMap.proj t) ∘ₗ
    GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (p + 1)

def one (s : X ⟶ Sp R) (D : κ → X.Opens) : (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X 0 :=
  fun t => GlobalTheory.AbLaw.SecOnR.of s _ _ ((GlobalTheory.AbLaw.secOnTrivEquiv _).symm 1)

def pr {X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i)
    (I : NE κ) : Pair ψ :=
  ⟨(cov D'' hD'' I, cov D' hD' I), show (⨅ i ∈ _, D'' i) ≤ ψ ⁻¹ᵁ (⨅ i ∈ _, D' i) by
    rw [GlobalTheory.AbLaw.preimage_biInf]; exact iInf₂_mono fun i _ => hle i⟩

def pullCoef {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'}
    {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) :
    CoefMap σ (covF s' D' hD') (covF s'' D'' hD'') where
  G := 𝟭 _
  α I := (pairPull w).α (op (pr D' hD' D'' hD'' hle I.unop))
  naturality {I J} f b := by
    have := (pairPull w).naturality (homOfLE (show pr D' hD' D'' hD'' hle J.unop ≤ pr D' hD' D'' hD'' hle I.unop from
      Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨(cov_mono D'' hD'') (leOfHom f.unop), (cov_mono D' hD') (leOfHom f.unop)⟩))).op b
    exact this
  smul I r b := (pairPull w).smul (op (pr D' hD' D'' hD'' hle I.unop)) r b

end Scheme

end GlobalTheory.CechPoset
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

open scoped nonZeroDivisors

theorem GlobalTheory.UCls.selfDual_latOf_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → ∃ L : Submodule (𝓞 E) (Fin r → E), (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) ∧ (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) ∧ SelfDualLat G L := by
  intro E _ _ _ r G Λ g0 hΛ hua
  obtain ⟨hG, hdet, hfg, hspan, hsd⟩ := hΛ
  obtain ⟨hunit, hpres⟩ := hua
  let g : GL (Fin r) (RA (maximalRealSubfield E) E) := Matrix.nonsingInvUnit g0 hunit
  have hg : (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) = g0 := rfl
  obtain ⟨L, hL, hLfg, hLspan, hLhat⟩ :=
    GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E r Λ g hfg hspan
  rw [hg] at hL hLhat
  have hmem : ∀ x : E, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ x := by
    intro x
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.isIntegral_coe
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hsd' : ∀ v : Fin r → E, (∀ y ∈ Λ, (∑ a, ∑ b, v a * G a b * (IsCMField.complexConj E) (y b)) ∈
      (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔ v ∈ Λ := by
    intro v
    simp only [hmem]
    exact hsd v
  have key := GlobalTheory.AdLat.latOf_selfDual (maximalRealSubfield E) E r Λ (IsCMField.complexConj E) G 1 g
    hfg hspan (IsCMField.complexConj_apply_apply E) hG hdet one_ne_zero hsd' (by rw [hg]; exact hpres)
  rw [hg] at key
  refine ⟨L, hL, hLhat, hG, hdet, hLfg, hLspan, fun x => ?_⟩
  have := key x
  rw [← hL] at this
  simp only [hmem, SetLike.mem_coe] at this
  exact this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletionStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_real_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → ∃ L : Submodule (𝓞 E) (Fin r → E), (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) ∧ (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) ∧ SelfDualLat G L := by
  first | exact @GlobalTheory.UCls.selfDual_latOf_translate | exact GlobalTheory.UCls.selfDual_latOf_translate | (intros; apply GlobalTheory.UCls.selfDual_latOf_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem ratM_mulVec_tmul (γ : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    ratM F γ *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (γ *ᵥ x) i := by
  ext i
  simp only [mulVec, dotProduct, ratM, Matrix.map_apply]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem ratM_mulVec_fv (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    ratM F γ *ᵥ fv F x = fv F (γ *ᵥ x) :=
  ratM_mulVec_tmul γ 1 x

theorem ratM_mul (γ δ : Matrix (Fin n) (Fin n) E) : ratM F (γ * δ) = ratM F γ * ratM F δ := by
  have h : ∀ ε : Matrix (Fin n) (Fin n) E,
      ratM F ε = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.mapMatrix ε := by
    intro ε; ext i j; simp [ratM]
  rw [h, h, h, map_mul]

theorem ratM_one : ratM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [ratM, Matrix.one_apply, h, Algebra.TensorProduct.one_def]

theorem fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  ext i; simp [fv, TensorProduct.tmul_sub]

theorem fv_nsmul (M : ℕ) (x : Fin n → E) : fv F (M • x) = M • fv F x := by
  ext i
  simp only [fv, Pi.smul_apply]
  exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E 1) M (x i)

theorem nsmul_cancel {V : Type} [AddCommGroup V] [Module F V] {M : ℕ} (hM : 1 ≤ M) {u w : V}
    (h : M • u = M • w) : u = w := by
  have h0 : (M : F) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  simpa [h0] using congrArg (fun z => (M : F)⁻¹ • z) h

theorem stab_cong_iff_hat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E) (hM : 1 ≤ M)
    (hrat : ∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) :
    ((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧
        ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔
      ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧
        ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x) := by
  set B : Matrix (Fin n) (Fin n) E := (β : Matrix (Fin n) (Fin n) E) with hB
  set C : Matrix (Fin n) (Fin n) E := ((β⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hC
  have hBC : B * C = 1 := Units.mul_inv β
  have hCB : C * B = 1 := Units.inv_mul β
  have hRBC : ∀ z, ratM F B *ᵥ (ratM F C *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hBC, ratM_one, one_mulVec]
  have hRCB : ∀ z, ratM F C *ᵥ (ratM F B *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hCB, ratM_one, one_mulVec]
  have gen : ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ Λ,
      (fun i => a ⊗ₜ[F] x i) ∈ hat F (Λ : Set (Fin n → E)) :=
    fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩
  constructor
  · rintro ⟨hstab, hcong⟩
    refine ⟨fun z hz => ?_, fun z hz => ⟨ratM F C *ᵥ z, ?_, hRBC z⟩⟩
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        obtain ⟨y, hy, hxy⟩ := hcong x hx
        refine ⟨fun i => a ⊗ₜ[F] y i, gen a ha y hy, ?_⟩
        rw [ratM_mulVec_tmul]
        ext i
        have := congrFun hxy i
        simp only [Pi.sub_apply, Pi.smul_apply] at this ⊢
        rw [← TensorProduct.tmul_sub, this]
        exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) M (y i)
      | zero => exact ⟨0, zero_mem _, by simp⟩
      | add z w _ _ h1 h2 =>
        obtain ⟨y1, hy1, e1⟩ := h1
        obtain ⟨y2, hy2, e2⟩ := h2
        refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
        rw [mulVec_add, smul_add, ← e1, ← e2]; abel
      | neg z _ h =>
        obtain ⟨y, hy, e⟩ := h
        refine ⟨-y, neg_mem hy, ?_⟩
        rw [mulVec_neg, smul_neg, ← e]; abel
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        rw [ratM_mulVec_tmul]
        refine gen a ha _ ((hstab _).2 ?_)
        rw [mulVec_mulVec, hBC, one_mulVec]; exact hx
      | zero => simp
      | add z w _ _ h1 h2 => rw [mulVec_add]; exact add_mem h1 h2
      | neg z _ h => rw [mulVec_neg]; exact neg_mem h
  · rintro ⟨hcong, hsurj⟩
    have himg : ∀ x ∈ Λ, B *ᵥ x ∈ Λ := by
      intro x hx
      obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      rw [← hrat, ← ratM_mulVec_fv, sub_eq_iff_eq_add.mp e]
      exact add_mem (nsmul_mem hy M) ((hrat x).2 hx)
    refine ⟨fun x => ⟨himg x, fun hx => ?_⟩, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := hsurj _ ((hrat _).2 hx)
      rw [← ratM_mulVec_fv] at e
      have hyx : y = fv F x := by
        have := congrArg (fun z => ratM F C *ᵥ z) e
        simpa only [hRCB] using this
      rw [← hrat, ← hyx]; exact hy
    · obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      set w : Fin n → E := (M : E)⁻¹ • (B *ᵥ x - x) with hw
      have hMw : M • w = B *ᵥ x - x := by
        rw [hw, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hM0]
      have hfw : fv F w = y := by
        apply nsmul_cancel (F := F) hM
        rw [← fv_nsmul, hMw, fv_sub, ← ratM_mulVec_fv, e]
      exact ⟨w, (hrat w).1 (hfw ▸ hy), hMw.symm⟩

end GlobalTheory.LocGlob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletionStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_congruence_iff_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E), 1 ≤ M → (∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) → (((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔ ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x)) := by
  first | exact @GlobalTheory.LocGlob.stab_cong_iff_hat | exact GlobalTheory.LocGlob.stab_cong_iff_hat | (intros; apply GlobalTheory.LocGlob.stab_cong_iff_hat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstant
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem frame_coord : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    CohomZeroIsConstants F → ∀ (n : ℕ) (Φ : Frame F n), ∃ l : Fin n → (Glob1 F →ₗ[R] R),
      (∀ i (w : Glob1 F) T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (l i w)) ∧
        ∀ w, w = ∑ i, l i w • Φ.w i := by
  intro R _ C _ F hF n Φ
  have hd : ∀ i (w : Glob1 F), d0 F (fun T ↦ Φ.δ i T (w.1 T)) = 0 := by
    intro i w
    funext T T' φ
    rw [amitsur_d0_apply, w.2 φ, Φ.nat]
    exact sub_self _
  let c : Fin n → Glob1 F → R := fun i w ↦ (hF _ (hd i w)).exists.choose
  have hc : ∀ i w T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (c i w) :=
    fun i w ↦ (hF _ (hd i w)).exists.choose_spec
  have uniq : ∀ i w (r : R), (∀ T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) r) → c i w = r :=
    fun i w r hr ↦ (hF _ (hd i w)).unique (hc i w) hr
  refine ⟨fun i ↦
    { toFun := c i
      map_add' := fun w w' ↦ uniq i (w + w') _ (fun T ↦ by
        rw [Submodule.coe_add, Pi.add_apply, map_add (f := _), hc, hc, map_add (f := _)])
      map_smul' := fun r w ↦ uniq i (r • w) _ (fun T ↦ by
        rw [Submodule.coe_smul, Pi.smul_apply, ← algebraMap_smul (F.obj T) r (w.1 T), map_smul, hc,
          RingHom.id_apply, smul_eq_mul, smul_eq_mul, map_mul]) },
    fun i w T ↦ hc i w T, fun w ↦ ?_⟩
  apply Subtype.ext
  funext T
  rw [Submodule.coe_sum, Finset.sum_apply]
  conv_lhs => rw [Φ.sum T (w.1 T)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hc, Submodule.coe_smul, Pi.smul_apply, algebraMap_smul]
  rfl

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalOneFormFrame_coordinates_constant : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), CohomZeroIsConstants F → ∀ (n : ℕ) (Φ : Frame F n), ∃ l : Fin n → (Glob1 F →ₗ[R] R), (∀ i (w : Glob1 F) T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (l i w)) ∧ ∀ w, w = ∑ i, l i w • Φ.w i := by
  first | exact @GlobalTheory.AbCoh.frame_coord | exact GlobalTheory.AbCoh.frame_coord | (intros; apply GlobalTheory.AbCoh.frame_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianS
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianS
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

open Opposite TopologicalSpace

theorem uConst_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → UConst A.hom := by
  intro R _ A _ hA R' _ _ X' s' φ hpb
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsm : Smooth s' := MorphismProperty.of_isPullback hpb ‹_›
  have hpr : IsProper s' := MorphismProperty.of_isPullback hpb ‹_›
  have hgc : GeometricallyConnected s' := MorphismProperty.of_isPullback hpb ‹_›
  haveI : GeometricallyIntegral s' :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected X' _ s' hsm hgc
  have hiso : IsIso s'.appTop := GlobalTheory.GlobalFunctions.isIso_app GlobalTheory.FlatFibreInjective.injective_baseChange
    GlobalTheory.exists_noetherian_model_of_smooth s' ⊤
  have hbij := ConcreteCategory.bijective_of_isIso s'.appTop
  intro g hg
  have hc : ∀ (U V : X'.affineOpens) (h : V.1 ≤ U.1),
      X'.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, htu⟩ := X'.sheaf.existsUnique_gluing' (fun U : X'.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top X').ge (fun U ↦ g (op U)) (by
      intro U V
      refine X'.sheaf.eq_of_locally_eq' (fun W : {W : X'.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens X'} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(X', a)),
            X'.presheaf.map f'.op (X'.presheaf.map f.op x) = X'.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))

  have hres : ∀ (r : R') (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r)) =
        algebraMap R' (Sec s' U.1) r := by
    intro r U
    rfl
  have hres' : ∀ (x : Γ(Sp R', ⊤)) (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop x) =
        algebraMap R' (Sec s' U.1) ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) := by
    intro x U
    have := hres ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) U
    rw [Iso.hom_inv_id_apply] at this
    exact this
  obtain ⟨r₀, hr₀⟩ := hbij.2 t
  subst hr₀
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R')).hom r₀, ?_, ?_⟩
  · intro U
    exact (ht U.unop).symm.trans (hres' r₀ U.unop)
  · intro r hr
    have h1 : s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r) = s'.appTop r₀ := by
      apply htu
      intro U
      exact (hres r U).trans (hr (op U)).symm
    have h2 := hbij.1 h1
    rw [← h2, Iso.inv_hom_id_apply]

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → UConst A.hom := by
  first | exact @GlobalTheory.AbCoh.uConst_of_isAbelianScheme | exact GlobalTheory.AbCoh.uConst_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.uConst_of_isAbelianScheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependent
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.Untwist

theorem res_X_isZero {R : Type} [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) :=
  (injectiveResolution F).cocomplex.isZero_extend_X ComplexShape.embeddingUpNat n (fun i hi => by
    change (i : ℤ) = n at hi; omega)

theorem sec_eq_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (y : Sec F U) : y = 0 := by
  have h := congrArg (fun φ : F ⟶ F => Sec.map φ y) (hF.eq_of_src (𝟙 F) 0)
  exact h

theorem sec_res_neg {R : Type} [CommRing R] (F : Shv R) {n : ℤ} (hn : n < 0) {U : Scheme.{0}} (y z : Sec ((res R F).X n) U) :
    y = z := (sec_eq_zero (res_X_isZero F n hn) y).trans (sec_eq_zero (res_X_isZero F n hn) z).symm

theorem cocycle_ext_zero {R : Type} [CommRing R] {X : Scheme.{0}} {F : Shv R}
    (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0)
    (h : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 0 (by simp) U x = ev β.1 0 0 (by simp) U x) : α = β := by
  refine Cocycle.ext (CupSpec.ev_ext _ _ fun p s hs U x => ?_)
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using hs.symm
    exact h U x
  | succ p => exact sec_res_neg F (by omega) _ _

theorem cup_rootClass {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (a b : ℤ) :
    cup q (rootClass a ζ) (rootClass b ζ) = (rootClass (a + b) ζ : Ht q (sch.obj X) (0 + 0) (a + b)) := by
  obtain ⟨α, hα, hα'⟩ := rootClass_spec a ζ
  obtain ⟨β, hβ, hβ'⟩ := rootClass_spec b ζ
  obtain ⟨γ, hγ, hγ'⟩ := rootClass_spec (a + b) ζ
  rw [← hα, ← hβ, ← hγ]
  refine Pair.cup_spec (twPair q a b) (sch.obj X) rfl α β γ ?_
  intro N w hw U x
  cases N with
  | zero =>
    obtain rfl : w = 0 := by simpa using hw.symm
    rw [Fin.sum_univ_one]
    change ev γ.1 0 0 _ U x = ((0 : ℤ) * 0).negOnePow • (twPair q a b).mul U 0 0 0 rfl (ev α.1 0 0 (by simp) U x) (ev β.1 0 0 (by simp) U x)
    have e1 : ev α.1 0 0 (by simp) U x = _ := hα' U x
    have e2 : ev β.1 0 0 (by simp) U x = _ := hβ' U x
    rw [e1, e2, mul_zero, Int.negOnePow_zero, one_smul]
    refine Eq.trans (hγ' U x) ?_
    change Sec.res (show U ⟶ X from x) _ = (twPair q a b).mul U 0 0 0 rfl (Sec.res (show U ⟶ X from x) _) (Sec.res (show U ⟶ X from x) _)
    rw [ClsSpec.res_resGen, ClsSpec.res_resGen, ClsSpec.res_resGen]
    exact (twPair_spec q a b U _).symm
  | succ N => exact sec_res_neg _ (by omega) _ _

theorem rootClass_zero {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (hX : Inv q (sch.obj X)) :
    rootClass 0 ζ = one q (sch.obj X) := by
  obtain ⟨α, hα, hα'⟩ := rootClass_spec 0 ζ
  obtain ⟨β, hβ, hβ'⟩ := one_spec q (sch.obj X) hX
  rw [← hα, ← hβ]
  refine congrArg CohomologyClass.mk (cocycle_ext_zero α β fun U x => ?_)
  rw [hα', hβ' U x (ζ.map x.appTop.hom), ClsSpec.res_resGen]

section Cast
variable {q : ℕ} {E : Spc}

theorem cast_cast {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (h₁ : n = n') (h₂ : i = i') (h₃ : n' = n'') (h₄ : i' = i'') :
    (x.cast h₁ h₂).cast h₃ h₄ = x.cast (h₁.trans h₃) (h₂.trans h₄) := by
  subst h₁; subst h₂; subst h₃; subst h₄; rfl

theorem cast_add {n i n' i' : ℤ} (x y : Ht q E n i) (hn : n = n') (hi : i = i') :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

theorem eq_cast_symm {n i n' i' : ℤ} {x : Ht q E n i} {y : Ht q E n' i'} (hn : n' = n) (hi : i' = i) (h : x = y.cast hn hi) :
    y = x.cast hn.symm hi.symm := by
  subst hn; subst hi; exact h.symm

theorem cup_cast_left {n m i j n' i' : ℤ} (x : Ht q E n i) (b : Ht q E m j) (hn : n = n') (hi : i = i') :
    cup q (x.cast hn hi) b = (cup q x b).cast (congrArg (· + m) hn) (congrArg (· + j) hi) := by
  subst hn; subst hi; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (a : Ht q E n i) (y : Ht q E m j) (hm : m = m') (hj : j = j') :
    cup q a (y.cast hm hj) = (cup q a y).cast (congrArg (n + ·) hm) (congrArg (i + ·) hj) := by
  subst hm; subst hj; rfl

theorem cup_cup_of_unit [NeZero q] (hE : Inv q E) {d e n i : ℤ} (u : Ht q E 0 d) (v : Ht q E 0 e) (hde : (0 : ℤ) = e + d)
    (hvu : cup q v u = (one q E).cast (by simp) hde) (a : Ht q E n i)
    {k : ℤ} (h₁ : 0 + n = n) (h₂ : d + i = k) (h₃ : 0 + n = n) (h₄ : e + k = i) :
    (cup q v ((cup q u a).cast h₁ h₂)).cast h₃ h₄ = a := by
  have hring := GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q E
  have hassoc := eq_cast_symm _ _ (hring.2.1 v u a)
  rw [cup_cast_right, cast_cast, hassoc, cast_cast, hvu, cup_cast_left, cast_cast, hring.1 hE a, cast_cast]
  rfl

end Cast

theorem rootClass_cast {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) {k k' : ℤ} (h : k = k') (hn : (0 : ℤ) = 0 + 0) :
    (rootClass k ζ).cast hn h = (rootClass k' ζ : Ht q (sch.obj X) (0 + 0) k') := by
  subst h; rfl

noncomputable def twistEquiv {q : ℕ} [NeZero q] {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (hX : Inv q (sch.obj X)) (n i j : ℤ) :
    Ht q (sch.obj X) n i ≃+ Ht q (sch.obj X) n j := by
  have key : ∀ d e : ℤ, ∀ hde : (0 : ℤ) = e + d,
      cup q (rootClass e ζ) (rootClass d ζ) = (one q (sch.obj X)).cast (by simp) hde := by
    intro d e hde
    rw [cup_rootClass, ← rootClass_zero ζ hX, rootClass_cast ζ hde]
  exact
    { toFun := fun a => (cup q (rootClass (j - i) ζ) a).cast (zero_add n) (by ring)
      invFun := fun b => (cup q (rootClass (i - j) ζ) b).cast (zero_add n) (by ring)
      left_inv := fun a => cup_cup_of_unit hX _ _ (by ring) (key _ _ (by ring)) a _ _ _ _
      right_inv := fun b => cup_cup_of_unit hX _ _ (by ring) (key _ _ (by ring)) b _ _ _ _
      map_add' := fun a b => by simp only [map_add (f := _), cast_add] }

end GlobalTheory.EtC.Untwist


open GlobalTheory.EtC.Untwist in
theorem GlobalTheory.EtC.untwist : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) →
    (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → ∀ n i j : ℤ, Nonempty (Ht q (sp A) n i ≃+ Ht q (sp A) n j) := by
  intro q _ A _ hq ⟨z, hz⟩ n i j
  let φ : A →+* Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hX : Inv q (sp A) := fun U ⟨x⟩ => by
    have h := (hq.map φ).map (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom
    simpa only [map_natCast] using h
  exact ⟨twistEquiv (Prim.map φ ⟨z, hq, hz⟩) hX n i j⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_spec_twist_independent : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → ∀ n i j : ℤ, Nonempty (Ht q (sp A) n i ≃+ Ht q (sp A) n j) := by
  first | (exact @GlobalTheory.EtC.untwist) | (exact GlobalTheory.EtC.untwist) | (intros; apply GlobalTheory.EtC.untwist  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.Vanish

theorem commAlgFunctorCohomologyTwo_eq_zero_of_isInitial {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {T₀ : C} (h : IsInitial T₀) (c : CatCoh.H2 F) : c = 0 := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  refine H2.mk_eq_zero.2 ⟨fun T T' φ ↦ z.1 T₀ T T' (h.to T) φ, ?_⟩
  funext T T' T'' φ ψ
  have := z.2 (h.to T) φ ψ
  rw [h.to_comp φ] at this
  rw [d1_apply]
  linear_combination this

theorem glob_sub {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T₀ : C}
    (h : IsInitial T₀) [Subsingleton Ω[F.obj T₀⁄R]] : Subsingleton (Glob1 F) :=
  subsingleton_of_forall_eq 0 fun ω ↦ Subtype.ext (funext fun T ↦ by
    rw [ω.2 (h.to T), Subsingleton.elim (ω.1 T₀) 0, map_zero]; rfl)

def topInit {X : Scheme.{0}} (hX : IsAffineOpen (⊤ : X.Opens)) : IsInitial (op ⟨⊤, hX⟩ : AffOp X) :=
  IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, hX⟩ from le_top (a := U.unop.1))).op)
    fun _ _ ↦ rfl

theorem omega_sub {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsIso s] :
    Subsingleton Ω[Sec s ⊤⁄R] := by
  refine KaehlerDifferential.subsingleton_of_surjective R _ ?_
  have : IsIso (secMap s ⊤) := by
    unfold secMap
    haveI h1 : IsIso s.appTop := inferInstanceAs (IsIso (s.app ⊤))
    haveI h2 : IsIso (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) := by
      rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl]
      infer_instance
    exact IsIso.comp_isIso' (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv) inferInstance
      (IsIso.comp_isIso' h1 h2)
  exact (ConcreteCategory.bijective_of_isIso (secMap s ⊤)).2

theorem main :
    (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsAffine X → Subsingleton (HO1 s) ∧ Subsingleton (HO2 s)) ∧
      ∀ (R : Type) [CommRing R], Subsingleton (GlobForm (𝟙_ (Over (Sp R))).hom) ∧
        Subsingleton (HH1 (𝟙_ (Over (Sp R))).hom) := by
  refine ⟨fun R _ X s hX ↦ ?_, fun R _ ↦ ?_⟩
  · have h := topInit (isAffineOpen_top X)
    exact ⟨subsingleton_of_forall_eq 0 (H1.eq_zero_of_isInitial _ h),
      subsingleton_of_forall_eq 0 (commAlgFunctorCohomologyTwo_eq_zero_of_isInitial _ h)⟩
  · haveI : IsIso (𝟙_ (Over (Sp R))).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))
    have h := topInit (isAffineOpen_top (Sp R))
    haveI : Subsingleton Ω[(OAff (𝟙_ (Over (Sp R))).hom).obj (op ⟨⊤, isAffineOpen_top (Sp R)⟩)⁄R] :=
      omega_sub (𝟙_ (Over (Sp R))).hom
    haveI hg : Subsingleton (GlobForm (𝟙_ (Over (Sp R))).hom) := glob_sub _ h
    refine ⟨hg, subsingleton_of_forall_eq 0 fun c ↦ ?_⟩
    have hc : c ∈ Fil1 (OAff (𝟙_ (Over (Sp R))).hom) := H1.eq_zero_of_isInitial _ h _
    rw [Fil1_eq_range] at hc
    obtain ⟨ω, rfl⟩ := hc
    have : ω = 0 := Subtype.ext (Subsingleton.elim (α := GlobForm (𝟙_ (Over (Sp R))).hom) _ _)
    rw [this, map_zero]

end GlobalTheory.AbCoh.Vanish
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitary
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.RatUnit


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.RatUnit.isUA_ratM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E), γ.det ≠ 0 → (∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (γ *ᵥ x) (γ *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) → _root_.GlobalTheory.UCls.IsUA (IsCMField.complexConj E) G (_root_.GlobalTheory.UCls.ratM (maximalRealSubfield E) γ) := by
  intro E _ _ _ r G γ hdet hinv
  have hmat : ∀ i j, ∑ a, ∑ b, γ a i * G a b * IsCMField.complexConj E (γ b j) = G i j := by
    intro i j
    have h := hinv (Pi.single i 1) (Pi.single j 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
    simpa [mulVec, dotProduct, Pi.single_apply, apply_ite] using h
  let A := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
  let φ : E →+* _root_.GlobalTheory.AdLat.RA (maximalRealSubfield E) E :=
    (Algebra.TensorProduct.includeRight :
      E →ₐ[maximalRealSubfield E] A ⊗[maximalRealSubfield E] E).toRingHom
  have hφ : ∀ e : E, φ e = (1 : A) ⊗ₜ[maximalRealSubfield E] e := fun _ => rfl
  have hg : _root_.GlobalTheory.UCls.ratM (maximalRealSubfield E) γ = γ.map φ := rfl
  let τ := _root_.GlobalTheory.AdLat.sg A (IsCMField.complexConj E)
  have hτ : ∀ e : E, τ (φ e) = φ (IsCMField.complexConj E e) := by
    intro e
    simp [τ, hφ, _root_.GlobalTheory.AdLat.sg]
  unfold _root_.GlobalTheory.UCls.IsUA
  rw [hg]
  refine ⟨?_, fun x y => ?_⟩
  · have h := RingHom.map_det φ γ
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (isUnit_iff_ne_zero.mpr hdet).map φ
  · unfold _root_.GlobalTheory.AdLat.hermA
    change ∑ a, ∑ b, (γ.map φ *ᵥ x) a * φ (G a b) * τ ((γ.map φ *ᵥ y) b) =
      ∑ a, ∑ b, x a * φ (G a b) * τ (y b)
    calc _ = ∑ a, ∑ b, ∑ i, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [mulVec, dotProduct, map_apply, map_sum, map_mul, hτ, Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ a, ∑ i, ∑ b, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ b,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ a, ∑ b,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, x i * φ (G i j) * τ (y j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← hmat i j, map_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [map_mul]

end GlobalTheory.RatUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitaryStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInvertibleUnitaryAdelicMatrix_of_rational_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E), γ.det ≠ 0 → (∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) → IsUA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) γ) := by
  first | exact @GlobalTheory.RatUnit.isUA_ratM | exact GlobalTheory.RatUnit.isUA_ratM | (intros; apply GlobalTheory.RatUnit.isUA_ratM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgProjectiveConstantRankExtensionAndProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgProjectiveConstantRankExtensionAndProd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem fp_prod (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup H] [Module R H] (a b : ℕ) (hW : FP R W a) (hH : FP R H b) :
    FP R (W × H) (a + b) := by
  obtain ⟨hWf, hWp, hWr⟩ := hW
  obtain ⟨hHf, hHp, hHr⟩ := hH
  refine ⟨inferInstance, inferInstance, fun p => ?_⟩
  have := Module.rankAtStalk_prod (R := R) W H
  rw [congrFun this p, Pi.add_apply, hWr p, hHr p]

theorem fp_ext (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ)
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hW : FP R W a) (hH : FP R H b) : FP R M (a + b) := by
  have hWH := fp_prod R W H a b hW hH
  obtain ⟨-, hHp, -⟩ := hH
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : H →ₗ[R] H) hp
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv hi ⟨s, hs⟩
  obtain ⟨hf, hpr, hr⟩ := hWH
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun q => ?_⟩
  rw [congrFun (Module.rankAtStalk_eq_of_equiv e) q, hr q]

theorem fp_ext_prod : (∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ) (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Injective i → Function.Surjective p → Function.Exact i p → FP R W a → FP R H b → FP R M (a + b)) ∧ ∀ (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W] [AddCommGroup H] [Module R H] (a b : ℕ), FP R W a → FP R H b → FP R (W × H) (a + b) :=
  ⟨fun R _ W M H _ _ _ _ _ _ a b i p hi hp hex hW hH => fp_ext R W M H a b i p hi hp hex hW hH,
   fun R _ W H _ _ _ _ a b hW hH => fp_prod R W H a b hW hH⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgProjectiveConstantRankExtensionAndProdStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod : (∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ) (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Injective i → Function.Surjective p → Function.Exact i p → FP R W a → FP R H b → FP R M (a + b)) ∧ ∀ (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W] [AddCommGroup H] [Module R H] (a b : ℕ), FP R W a → FP R H b → FP R (W × H) (a + b) := by
  first | exact @GlobalTheory.AbCoh.fp_ext_prod | exact GlobalTheory.AbCoh.fp_ext_prod | (intros; apply GlobalTheory.AbCoh.fp_ext_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfFormInjectiveOfH0Const
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem ofForm_injective_of_H0Const (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hF : CohomZeroIsConstants F) : Function.Injective (ofForm F) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ω hω
  obtain ⟨g, hg, hD⟩ := (ofForm_eq_zero (F := F)).1 hω
  have h0 : d0 F g = 0 := by
    funext T T' φ
    have e : d0 F g T T' φ = g T' - mp F φ (g T) := rfl
    rw [e, ← hg φ, sub_self]; rfl
  obtain ⟨r, hr, -⟩ := hF g h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  rw [← hD T, hr T]
  exact (D R (F.obj T)).map_algebraMap r

end GlobalTheory.AbCoh
end
