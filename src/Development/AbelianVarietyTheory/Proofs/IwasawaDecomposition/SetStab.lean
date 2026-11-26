module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

def bar {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (q : PtY ST SG Q y) (w : SG) :
    Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal) :=
  {v | ∃ z ∈ q.1.2, v = q.1.1.deco.1.be w ((qOf w.1 : X.E) • z)}

def setStab {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) : Subgroup (GL (Fin n) κ) where
  carrier := {h | ∀ v, h.1 *ᵥ v ∈ C ↔ v ∈ C}
  one_mem' v := by simp
  mul_mem' {a b} ha hb v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  inv_mem' {a} ha v := by
    rw [← ha, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.MemChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.RegCrit

theorem isUnit_of_one_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (c : e.O)
    (hc : 1 ≤ e.w c) : IsUnit c := by
  have h0 : (c : AlgebraicClosure F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact absurd hc (by norm_num)
  have h1 : (c : AlgebraicClosure F)⁻¹ ∈ e.O := by
    rw [e.mem_O, map_inv₀]
    exact inv_le_one_of_one_le₀ hc
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ h0))

end GlobalTheory.TrueGeo.RegCrit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfIffUnitaryDecoration
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.PtDeco

theorem isPtOf_iff_decoRaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), Q = ∅ → (IsPtOf hc g p ↔ g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g p hQ
  subst hQ
  have hlast : ∀ i : Fin n, i.1 + 1 = n → lastIdx n = i := fun i hi => Fin.ext (by simp [lastIdx]; omega)
  constructor
  · intro h
    have hg : g ∈ UAd hc n := h.uni
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by
      have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
        let L := p.deco.1.N
        let W := Submodule.span E (L : Set (Sp E n))
        change W = ⊤
        by_contra hW
        let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
        let f : Sp E n →ₗ[E] Module.Dual E W :=
          (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
        have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
          rw [Subspace.dual_finrank_eq]
          exact Submodule.finrank_lt hW
        obtain ⟨x, hx, hx₀⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
        have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
        have hsmul (a : E) : a • e x ∈ L := by
          rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
          intro y hy
          apply hStd_mem_one_symm
          have hxy : hStd E n (e x) y = 0 :=
            congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
          simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
        let i : E →ₗ[𝓞 E] L :=
          ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
        let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
        let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
          smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
        exact RingOfIntegers.not_isField E
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
      have h1 := Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg)
        hspan
      ext v
      conv_lhs => rw [← h1]
      have e1 : ∀ (x : GL (Fin n) (AfE F E)) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E),
          v ∈ Formalism.UG.CS.globLat x Λ ↔ ((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        fun _ _ _ => Iff.rfl
      rw [e1, e1, inv_one, Units.val_one, Matrix.one_mulVec]
      exact h.lat _
    refine ⟨hg, Deco.Ok.ext_on p.deco.2 (decorated_lattice_exists hc n ST SG g hg) hN (fun P x hx => ?_) (fun w x hx => ?_)⟩
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      refine HasRes.unique (h.f P x hx (lastIdx n) (by simp [lastIdx]; have := NeZero.pos n; omega)) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' _)
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      funext i
      refine HasRes.unique (h.be w x hx i) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' i)
  · rintro ⟨hg, hd⟩
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by rw [hd]; rfl
    refine ⟨hg, hN ▸ PtExist.carries_globLat g, fun P x hx i hi => ?_, fun w x hx i => ?_,
      fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx), hlast i hi]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx)]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)

end GlobalTheory.Mem.Col2.PtDeco

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section
namespace GlobalTheory.Mem.Col2.RatMove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ}


omit [NumberField E] [StarRing E] in
theorem glEquiv_apply_mulVec (g : GL (Fin n) E) (x : Sp E n) : Formalism.UG.glEquiv g x = (g : Matrix (Fin n) (Fin n) E) *ᵥ x := by
  simp [Formalism.UG.glEquiv]

theorem ufGL_eq (γ : UF E n) : ufGL E n γ = (((ratEquiv hc n).symm γ : URat hc n) : GL (Fin n) E) := by
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun j => ?_
  funext i
  have h1 := congrArg (fun g : UF E n => (g : Sp E n ≃ₗ[E] Sp E n) (Pi.single j 1) i) hγ
  simp only [ratHom, MonoidHom.coe_mk, OneHom.coe_mk] at h1
  rw [← glEquiv_apply_mulVec, ← glEquiv_apply_mulVec, h1]
  show Formalism.UG.glEquiv (toGLm E n γ.1) _ i = _
  rw [glEquiv_toGLm]


omit [NumberField E] [StarRing E] in
theorem glEquiv_symm_apply (γ : GL (Fin n) E) (v : Sp E n) :
    (Formalism.UG.glEquiv γ).symm v = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v := by
  rw [LinearEquiv.symm_apply_eq]
  simp [Formalism.UG.glEquiv, Matrix.mulVec_mulVec]

theorem pullV_ratMul (γ : GL (Fin n) E) (g : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (Formalism.UG.bc (iA F E) γ * g) x = GlobalTheory.Mem.Col2.pullV g ((Formalism.UG.glEquiv γ).symm x) := by
  have h := Formalism.L2.Col.pullV_rawSm γ g 1 x
  rw [inv_one, mul_one, Units.val_one, Matrix.one_mulVec] at h
  rw [glEquiv_symm_apply]
  exact h

variable {hc} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem isPtOf_ratMul (γ : URat hc n) {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    IsPtOf hc (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
      (((ratHom hc n γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
    let L := p.deco.1.N
    let W := Submodule.span E (L : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let f : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
    have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
    have hsmul (a : E) : a • e x ∈ L := by
      rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) hspan]
    ext w
    refine (h.lat _).symm.trans ?_
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hst : (1 : GL (Fin n) (AfE F E))⁻¹ ∈
      Formalism.UG.stabGL (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n)) := by
    rw [inv_one]; exact one_mem _
  have hN2 := Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) (stdLat E n) γ g _ hst
  rw [inv_one, mul_one] at hN2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (ratIn hc n γ).2 h.uni
  · have hc2 := PtExist.carries_globLat (F := F) (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
    rw [hN2, hN] at hc2
    exact hc2
  · intro P x hx i hi
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    rw [pullV_ratMul]
    exact h.f P _ hx' i hi
  · intro w x hx i
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    show HasRes w.1 _ (((((1 : GLG (E := E) (n := n) (SG := SG)) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) *ᵥ
      p.deco.1.be w ((Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x)) i)
    rw [Pi.one_apply, Units.val_one, Matrix.one_mulVec, pullV_ratMul]
    exact h.be w _ hx' i
  · intro P i j
    show _ = algebraMap E _ ((Formalism.UG.glEquiv (γ : GL (Fin n) E) * p.fr P * (((1 : GLQ E n Q) P)⁻¹).1) (Pi.single j 1) i)
    have e1 : (((1 : GLQ E n Q) P)⁻¹).1 = 1 := by simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, mul_one, LinearEquiv.mul_apply, glEquiv_apply_mulVec, Units.val_mul, Matrix.mul_apply, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.fr P l j]
    congr 1
    show adAt F P.1 (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ : GL (Fin n) E) i l)) = _
    rw [adAt_inclE]

theorem isPtOf_ratAd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E))
    (p : DecoF E n ST SG Q), IsPtOf hc g p →
      IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  intro F E _ _ _ _ _ _ hc n ST SG Q γ g p h
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  have hR : ratAd F γ = Formalism.UG.bc (iA F E) ((((ratEquiv hc n).symm γ : URat hc n)) : GL (Fin n) E) := by
    show Formalism.UG.bc (iA F E) (ufGL E n γ) = _
    rw [ufGL_eq hc]
  have := isPtOf_ratMul ((ratEquiv hc n).symm γ) (ST := ST) (SG := SG) (Q := Q) h
  rw [hγ] at this
  rw [hR]
  exact this

end GlobalTheory.Mem.Col2.RatMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMulStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPointOf_rational_unitary_adelic_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), IsPtOf hc g p → IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  first | exact @GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd | (intros; apply GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.FormSym

theorem mem_FiC_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n)
    {c c' : Type} (yc : c → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (e : c' → c) (he : Function.Surjective e)
    (g : c → Frames (gramC J emb) → ℂ) :
    g ∘ e ∈ FiC S emb lam (yc ∘ e) ↔ g ∈ FiC S emb lam yc := by
  simp only [FiC, Submodule.mem_map]
  constructor
  · rintro ⟨h, hh, he'⟩
    refine ⟨h, hh, ?_⟩
    funext x
    obtain ⟨x', rfl⟩ := he x
    exact congrFun he' x'
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

section Gen

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}

def clsOfChart (β : Ch) (hβ : ∀ c, chOf c = β)
    (K : LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) : ClsTied u i hi where
  lev := K.lev
  y c := K.y ⟨c, hβ c⟩
  y_bij := K.y_bij.comp (f := fun c : (D.mem u).C.cls i => (⟨c, hβ c⟩ : {c // chOf c = β}))
    ⟨fun _ _ h => congrArg Subtype.val h, fun c => ⟨c.1, rfl⟩⟩
  y_lat c := K.y_lat ⟨c, hβ c⟩
  stabI c := K.stabI ⟨c, hβ c⟩
  stabI_inj c := K.stabI_inj ⟨c, hβ c⟩
  stabI_range c := K.stabI_range ⟨c, hβ c⟩


set_option maxHeartbeats 4000000 in
def valOfG [Subsingleton Ch] (eV : (D.mem u).A.vT ≃ PlT D u)
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)
    (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (hde : ∃ C : GL (Fin (D.R.N i)) D.host.E,
      cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
      (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
      ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eY z).1 τ).det)
    (hV : ValuationCompatibleChart (D.fm u) eY (fun _ => True) chOf (lat := fun c => clsCrd D u i hi c) K)
    (hI : IpVTieG (D.fm u) eY)
    (hD : DilationCompatibleChart (D.fm u) eY eV chOf (lat := fun c => clsCrd D u i hi c) K) :
    ValTied u eV i hi (clsOfChart β hβ (K β)) where
  eY := eY
  de := hde
  Fi φ := by
    rw [hV.Fi φ]
    constructor
    · intro h
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).2 (h β)
    · intro h β'
      obtain rfl : β = β' := Subsingleton.elim _ _
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).1 h
  ipV := hI
  rat := hV.rat
  lat x := by
    constructor
    · intro hx w
      exact (hV.lat w trivial x).1 (Submodule.subset_span hx)
    · intro h
      exact GlobalTheory.LvT.mem_of_forall_locW D _ (fun w => (hV.lat w trivial x).2 (h w))
  dil v a k hk c δ hδ := hD.dil v a k hk β ⟨c, hβ c⟩ δ hδ
  dilT v a k hk c δ hδ g hg := hD.dilT v a k hk β ⟨c, hβ c⟩ δ hδ g hg


set_option maxHeartbeats 4000000 in
def lvOfG (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c)) :
    LvTied u A i hi where
  pr := L.pr
  pr_surj := L.pr_surj
  pr_smul := L.pr_smul
  pr_ker := L.pr_ker
  fv_ker := L.fv_ker
  prk := L.prk
  prk_surj := L.prk_surj
  prk_smul := L.prk_smul
  prk_ker := L.prk_ker
  te := L.te

variable (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c))
  (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)

set_option maxHeartbeats 4000000 in
theorem fvOfG (fMe : ∀ β v, (K β).lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (h : FvTieG L A.eV K fMe) :
    FvTie (lvOfG A L) (clsOfChart β hβ (K β)) (fMe β) :=
  fun v c z hz => h v β ⟨c, hβ c⟩ z hz

set_option maxHeartbeats 4000000 in
theorem upOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : UpNatTieG L eY A.eV K) : UpNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c z hz
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := h v β ⟨c, hβ c⟩ z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun g s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 g s s' hs

set_option maxHeartbeats 4000000 in
theorem dnOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : DnNatTieG L eY A.eV K) : DnNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c g hg
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h6⟩ := h v β ⟨c, hβ c⟩ g hg
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun f s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 f s s' hs

end Gen

section Gen2

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 4000000 in
theorem normOfG {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u eV i hi K) (hY : W.eY = eY) (h : NormTieG (D.fm u) eY) : NormTie W := by
  intro s x Pc hPc o ho
  rw [hY] at hPc
  exact h s x Pc hPc o ho

set_option maxHeartbeats 4000000 in
theorem bwOfG (A : AtTTied u) {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u A.eV i hi K) (hY : W.eY = eY)
    (h : BwTieG (D.fm u) (D.mem u).A.T A.res eY (fun c => clsCrd D u i hi c)) : BwTie A W := by
  intro w hw hs v x
  rw [hY]
  exact h w hw hs v x

end Gen2


set_option maxHeartbeats 4000000 in
theorem readsK_one {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {u : B.Word} {a : I.ι}
    {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))} (h : I.ReadsK l Z u a i hi chOf K) (β : Ch)
    (hβ : ∀ c, chOf c = β) :
    ∃ k, I.Reads u a i (fun _ => ()) (fun _ => (K β).lev.Lb) (fun _ => (K β).lev.U) (fun _ => (K β).lev.chi)
      (fun c => ((K β).y ⟨c, hβ c⟩).1) (fun c s => ((K β).stabI ⟨c, hβ c⟩ s).1) k := by
  obtain rfl : chOf = fun _ => β := funext hβ
  obtain ⟨k, hk⟩ := h
  refine ⟨fun _ => k β, ⟨fun c c' => ⟨fun _ => (hk.key c c').1 rfl, fun _ => rfl⟩, fun _ => ?_, fun _ => hk.lb β,
    fun _ => hk.k_std β, fun _ => hk.k_off β, fun _ => hk.k_T β, hk.pt, hk.lev, hk.chr, hk.stab⟩⟩
  obtain ⟨c, _⟩ := hk.onto β
  exact ⟨c, rfl⟩

end GlobalTheory.Mem.FormSym

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.dtTied_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ T : Formalism.L2.Host.DtTied (I.rec7 l Z) (I.cf l Z), ∀ a, T.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ) := by
  intro B X I _ _ l Z
  refine ⟨GlobalTheory.Mem.Col2.dtIsoRational (I.rec7 l Z) (I.cf l Z) I.SQ (MulEquiv.refl _) (fun j => rfl) rfl ?_ (fun z => rfl), fun _ => rfl⟩
  show UOQ B.host I.SQ = _
  ext x
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChart
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def Chart (u : B.Word) (a : I.ι) (i : ℕ) : Type :=
  Set.range fun c : (I.stp u a i).Cl => (c.1, cosetIn ((I.stp u a i).rep c))

def chartOf (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : Chart I u a i :=
  ⟨(c.1, cosetIn ((I.stp u a i).rep c)), c, rfl⟩

structure AdmK (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} (k : Ch → GA B (B.R.N i)) : Prop where
  std : ∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (k β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)
  off : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
    (a = I.mu0 ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (k β) = 1
  T : ∀ β (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
    HasRes P.1 (adAt B.host.F P.1 (((k β)⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)

theorem finite_chart (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) : Finite (Chart I u a i) := by
  have h := (l.ch u a).step i
  haveI : Finite (I.stp u a i).Cl := @Finite.instSigma _ _ inferInstance h.fin_orb
  exact (Set.finite_range _).to_subtype

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.IpMt

theorem ipMt_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (jM : (I.per l u a).Mt →ₛₗ[starRingEnd ℂ] (I.per l u a).Wrow), (∀ F, jM F ∈ (I.fm l u a).ptC) → (∀ w F, (I.per l u a).period w F = (I.fm l u a).ipP (jM F) w) → (∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F)) ∧ ∀ F, F ≠ 0 → 0 < (I.ipMt l u a F F).re := by
  intro B X I hOk hP l Z u a jM hmem hper
  obtain ⟨j0, hinj, -, hmem0, hper0, hpos⟩ := PerConj.period_conj I hOk hP l Z u a
  have uniq : ∀ z ∈ (I.fm l u a).ptC, ∀ z' ∈ (I.fm l u a).ptC,
      (∀ w, (I.fm l u a).ipP z w = (I.fm l u a).ipP z' w) → z = z' := by
    intro z hz z' hz' h
    by_contra hne
    have h1 := hpos _ (sub_mem hz hz') (sub_ne_zero.2 hne)
    rw [map_sub (I.fm l u a).ipP, LinearMap.sub_apply, h, sub_self] at h1
    simp at h1
  have hj : ∀ G, I.jStd l u a G = jM G := by
    intro G
    have hex : ∃ z, z ∈ (I.fm l u a).ptC ∧ ∀ w, (I.per l u a).period w G = (I.fm l u a).ipP z w :=
      ⟨jM G, hmem G, fun w => hper w G⟩
    have hs := Classical.epsilon_spec hex
    exact uniq _ hs.1 _ (hmem G) fun w => (hs.2 w).symm.trans (hper w G)
  have hform : ∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F) := by
    intro F G
    rw [TC.ipMt, hj, hj]
  refine ⟨hform, fun F hF => ?_⟩
  have h0 : jM F = j0 F := uniq _ (hmem F) _ (hmem0 F) fun w => (hper w F).symm.trans (hper0 w F)
  have hne : jM F ≠ 0 := by
    rw [h0]
    exact fun h => hF (hinj (h.trans (map_zero j0).symm))
  rw [hform]
  exact hpos _ (hmem F) hne

theorem ipMt_sum {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (F G : (I.perIn u a).Mt B.fields.emb B.embLL) :
    I.ipMt l u a F G = letI := (I.perIn u a).clFin (l.per u a);
      ∑ c, (I.perIn u a).wt c * pairB (I.perIn u a).sgT
        (MvPolynomial.map (starRingEnd ℂ) (F.1 c.1 ((I.perIn u a).S'.rep c))) (G.1 c.1 ((I.perIn u a).S'.rep c)) := by
  have hE : ∀ τ x, embAt B.embLL B.fields.emb τ (letI := B.fields.starE; star x) =
      starRingEnd ℂ (embAt B.embLL B.fields.emb τ x) := fun τ x => (GlobalTheory.Mem.FieldsLaws.fields_ok B).conjE _ x
  have hH : ∀ b, (I.perIn u a).H b = ⊤ := fun _ => rfl
  have h := (ipMt_tie I hOk hP l Z u a (PerConj.jM (I.perIn u a) B.fields.emb B.embLL)
    (PerConj.jM_mem _ _ hE (l.per u a) hH)
    (PerConj.period_eq _ _ (l.ch u a) (l.per u a) (B.hcW u))).1 F G
  refine h.trans ?_
  refine (PerConj.petersson_apply B.fields.emb B.embLL (l.per u a) _ _).trans ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (PerConj.ipVal_cev _ _ _ _ _).trans (congrArg (fun p => pairB _ p _) (PerConj.polOf_cev _ _ _ _))

end GlobalTheory.Mem.Col2.IpMt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowForms
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
open GlobalTheory.TopStep Formalism.HermitianLatticesTheory
noncomputable section

namespace GlobalTheory.Mem.Df

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (C : ChainIn X.E X.K X.Tau R) (b0 : (C.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (C.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (C.S R.m).G b0) (tz : X.E)

@[reducible] def perStepX : PerIn C where
  S' := stepX Ch sel mu P
  b0 := b0
  til := til
  ext := ext
  sg := W.sgW
  tz := tz
  H _ := ⊤

variable (σ : X.K →+* ℂ)

theorem mem_perStepX_Mt (F : ∀ b, (stepX Ch sel mu P).D b → Pol ℂ X.Tau (R.N R.m - 1)) :
    F ∈ (perStepX W Ch sel mu P C b0 til ext tz).Mt X.emb σ ↔
      FrLaw σ W.sgTrue (rowTyG Ch P) (levQX R sel mu) ⊤ fun p : XPt Pr R sel mu => F () (trivPt X _ _ _ _ p) := by
  constructor
  · intro h p
    refine ⟨(h () _).1, fun g hg => ?_⟩
    show F () (trivPt X _ _ _ _ (g • p)) = _
    rw [← stepX_smul_trivPt]
    exact (h () (trivPt X _ _ _ _ p)).2 g hg
  · rintro h ⟨⟩ d
    obtain ⟨p, rfl⟩ := (trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).surjective d
    refine ⟨(h p).1, fun g hg => ?_⟩
    exact (congrArg (F ()) (stepX_smul_trivPt Ch sel mu P g p)).trans ((h p).2 g hg)

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))

def mtEquivStepX : MtP W Ch sel mu P σ ≃ₗ[ℂ] (perStepX W Ch sel mu P C b0 til ext tz).Mt X.emb σ :=
  LinearEquiv.ofBijective
    { toFun := fun F => ⟨fun _ p => F.1 (toRow sel mu p.1.1),
        (mem_perStepX_Mt W Ch sel mu P C b0 til ext tz σ _).2
          ((frLaw_comp_iff σ W.sgTrue (isSubLev_top (rowTyG Ch P) (levQX R sel mu)) hd F.1).2 F.2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨fun F G h => Subtype.ext (funext fun d => by
      obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
      exact congrFun (congrFun (congrArg Subtype.val h) ()) (trivPt X _ _ _ _ p)),
    fun F => by
      obtain ⟨G, hG, e⟩ := ((mem_perStepX_Mt W Ch sel mu P C b0 til ext tz σ F.1).1 F.2).exists_form σ W.sgTrue
        (isSubLev_top (rowTyG Ch P) (levQX R sel mu)) hd
      refine ⟨⟨G, hG⟩, Subtype.ext (funext fun _ => funext fun p => (e p.1.1).trans ?_)⟩
      exact congrArg (F.1 ()) ((trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).apply_symm_apply p)⟩

end General

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem disjoint_vGs_Q (hI : I.Ok) (l : I.Laws) (a : I.ι) : Disjoint (B.primes X).vGs (I.Q a) :=
  GlobalTheory.NormOneUnit.disjoint_vGs_QE (I.tup a) l.pr hI.sel_ok (fun i => hI.g_mem i)

theorem mtCx_equiv_per : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok),
    ∀ (u : B.Word) (a : I.ι), ∃ g : MtCx I a ≃ₗ[ℂ] (I.per l u a).Mt, ∀ F, SameForm I l u a F (g F) := by
  intro B X I hI _ l _ u a
  let g := mtEquivStepX B.wts I.Ch I.sel (I.tup a) I.Ps (I.chIn u a) (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext
    (I.perIn u a).tz B.embLL (disjoint_vGs_Q I hI l a)
  exact ⟨g, fun F p => rfl⟩

end GlobalTheory.Mem.Df

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowFormsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tupleUnitaryForms_equiv_periodRowForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), ∀ (u : B.Word) (a : I.ι), ∃ g : MtCx I a ≃ₗ[ℂ] (I.per l u a).Mt, ∀ F, SameForm I l u a F (g F) := by
  first | exact @GlobalTheory.Mem.Df.mtCx_equiv_per | exact GlobalTheory.Mem.Df.mtCx_equiv_per | (intros; apply GlobalTheory.Mem.Df.mtCx_equiv_per <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaLiftContinuousInvariantHasDerivAt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaLiftContinuousInvariantHasDerivAt
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftDer

theorem hasDerivAt_integral_of_cocompact {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K K' : ℝ → H → ℂ)
    (hK : ∀ t, Continuous (K t)) (hK' : Continuous fun p : ℝ × H => K' p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ t h, K t (γ * h) = K t h) (hinv' : ∀ γ ∈ Γ, ∀ t h, K' t (γ * h) = K' t h)
    (hd : ∀ t h, HasDerivAt (fun s => K s h) (K' t h) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ h in 𝓕, K t h ∂μ) (∫ h in 𝓕, K' t₀ h ∂μ) t₀ := by
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds t₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hK'.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕) := by
    have h := hconst.re
    change Integrable (fun _ : H => Complex.re (M : ℂ)) (μ.restrict 𝓕) at h
    simpa only [Complex.ofReal_re] using h
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => M) hN₀
    (Filter.Eventually.of_forall fun t => (hK t).aestronglyMeasurable)
    (GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ (hK t₀) (fun γ hγ h => hinv γ hγ t₀ h))
    (hK'.comp (Continuous.prodMk_right t₀)).aestronglyMeasurable ?_ hconst'
    (Filter.Eventually.of_forall fun h t _ => hd t h)).2
  refine Filter.Eventually.of_forall fun h t ht => ?_
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
  rw [hinv' γ hγ]
  exact hM (t, c) ⟨ht, hc⟩

theorem kernel_continuous_invariant {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (L : X →ₗ[ℂ] (WO S T → ℂ)) (hL : ∀ x, IsThetaFunO ψ S T (L x)) {F : GA D S → X} (hF : Continuous F)
    (hinv : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) :
    (Continuous fun p : GA D T × GA D S => thetaKO om p.2 p.1 (L (F p.2))) ∧
      (∀ γ ∈ GQ S, ∀ g h, thetaKO om (γ * h) g (L (F (γ * h))) = thetaKO om h g (L (F h))) ∧
      ∀ γ ∈ GQ T, ∀ g h, thetaKO om h (γ * g) (L (F h)) = thetaKO om h g (L (F h)) := by
  refine ⟨?_, fun γ hγ g h => ?_, fun γ hγ g h => ?_⟩
  · let b := Module.finBasis ℂ X
    have e : (fun p : GA D T × GA D S => thetaKO om p.2 p.1 (L (F p.2))) =
        fun p => ∑ k, b.coord k (F p.2) * om (p.2, p.1) (L (b k)) 0 := by
      funext p
      conv_lhs => rw [← b.sum_repr (F p.2)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    rw [e]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_
    · exact ((b.coord k).continuous_of_finiteDimensional.comp hF).comp continuous_snd
    · exact (hom.om_cont _ (hL (b k)) 0).comp continuous_swap
  · have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 γ hγ 1 (one_mem _) h g
    rw [one_mul] at this
    rw [hinv γ hγ, this]
  · have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 1 (one_mem _) γ hγ h g
    rwa [one_mul] at this

theorem lift_continuous_invariant_hasDerivAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (Continuous (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ γ ∈ GQ T, ∀ g, lift om ν 𝓕 (fun h => L (F h)) (γ * g) = lift om ν 𝓕 (fun h => L (F h)) g) ∧ ∀ τ, ∀ Y ∈ lieAt T τ, ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧ (∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x)) (thetaKO om h g (L' x)) 0) ∧ ∀ g, HasDerivAt (fun t : ℝ => lift om ν 𝓕 (fun h => L (F h)) (g * oneP θ T τ Y t)) (lift om ν 𝓕 (fun h => L' (F h)) g) 0 := by
  intro D ψ S T χS χT om hom θ hθ hpos X _ _ _ L hL F hF hinv ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  obtain ⟨hc, hiS, hiT⟩ := kernel_continuous_invariant hom L hL hF hinv
  refine ⟨⟨?_, fun γ hγ g => ?_⟩, fun τ Y hY => ?_⟩
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun g h => thetaKO om h g (L (F h))) hc hiS
  · simp only [GlobalTheory.DefLift.lift, hiT γ hγ]
  · obtain ⟨Gn, hGn⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ Y hY
    have hL' : ∀ x, IsThetaFunO ψ S T ((Gn ∘ₗ L) x) := fun x => (hGn _ (hL x)).1
    have hd : ∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x))
        (thetaKO om h g ((Gn ∘ₗ L) x)) 0 := by
      intro x h g
      have := (hGn _ (hL x)).2.2.2 (h, g) 0
      simp only [Prod.mk_mul_mk, mul_one] at this
      exact this
    refine ⟨Gn ∘ₗ L, hL', hd, fun g => ?_⟩
    obtain ⟨hc', hiS', -⟩ := kernel_continuous_invariant hom (Gn ∘ₗ L) hL' hF hinv
    have hp : Continuous fun t : ℝ => g * oneP θ T τ Y t :=
      continuous_const.mul (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
    have key := hasDerivAt_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun t h => thetaKO om h (g * oneP θ T τ Y t) (L (F h)))
      (fun t h => thetaKO om h (g * oneP θ T τ Y t) ((Gn ∘ₗ L) (F h)))
      (fun t => hc.comp (Continuous.prodMk_right (g * oneP θ T τ Y t)))
      (hc'.comp (hp.prodMap continuous_id))
      (fun γ hγ t h => hiS γ hγ _ h) (fun γ hγ t h => hiS' γ hγ _ h)
      (fun t h => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hY (φ := fun g => thetaKO om h g (L (F h)))
        (φ' := fun g => thetaKO om h g ((Gn ∘ₗ L) (F h))) (hd (F h) h) g t) 0
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
    exact key

end GlobalTheory.DefLiftDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaLiftContinuousInvariantHasDerivAtStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteThetaLift_continuous_invariant_hasDerivAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (Continuous (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ γ ∈ GQ T, ∀ g, lift om ν 𝓕 (fun h => L (F h)) (γ * g) = lift om ν 𝓕 (fun h => L (F h)) g) ∧ ∀ τ, ∀ Y ∈ lieAt T τ, ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧ (∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x)) (thetaKO om h g (L' x)) 0) ∧ ∀ g, HasDerivAt (fun t : ℝ => lift om ν 𝓕 (fun h => L (F h)) (g * oneP θ T τ Y t)) (lift om ν 𝓕 (fun h => L' (F h)) g) 0 := by
  first | exact @GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt | exact GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt | (intros; apply GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

theorem IsAmpleLB.tens_of_isNef : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, GlobalTheory.IsAmpleLB A → (letI := GlobalTheory.algebraΓOfHom f; GlobalTheory.IsNef k N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens A N) := by
  intro h k _ X f hf A N hA hN
  letI := GlobalTheory.algebraΓOfHom f
  refine IsAmpleLB.tens_of_forall_isPsEff k X f hf A N hA hN.isLB fun Z hZ => ?_
  haveI := isIntegral_red hZ
  letI := algebraΓAlong k (redι Z)
  have hi := appTop_algebraMap_along k (redι Z)
  have hp : IsProjOver (strHom k (X := X)) := by rwa [strHom_eq (f := f) fun _ => rfl]
  have hp' : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    obtain ⟨n, e, he, hs⟩ := hp
    exact ⟨n, redι Z ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩
  exact IsNef.isPsEff h k _ hp' _ (hN.pull_of_isClosedImmersion (redι Z) hi)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df


set_option maxHeartbeats 1600000 in
theorem cols_ipV_herm {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (c : ((I.cols l).mem u).C.cls 0)
    (f g : ((I.cols l).mem u).C.Y 0 → ℂ) :
    ((I.cols l).fm u).ipV 0 c f g = starRingEnd ℂ (((I.cols l).fm u).ipV 0 c g f) :=
  ClassSumPos.ipVal_herm _ _ _ f g

theorem cols_ipC_herm {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word)
    (φ ψ : ((I.cols l).mem u).C.cls 0 → ((I.cols l).mem u).C.Y 0 → ℂ) :
    starRingEnd ℂ (((I.cols l).fm u).ipC 0 ψ φ) = ((I.cols l).fm u).ipC 0 φ ψ := by
  unfold MemberForms.ipC
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, cols_ipV_herm I l u c (φ c) (ψ c)]
  congr 1
  simp [ColumnChain.wt]

theorem cols_pos : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok),
    SpectralModel.ColsPos (I.cols l) := by
  intro B X I _ _ l _ u
  refine ⟨fun x _ y _ => cols_ipC_herm I l u x y, fun x hx h0 => ?_⟩
  exact ipC_zero_re_pos B (I.cols l) u (fun φ ψ => (cols_ipC_herm I l u ψ.1 φ.1).symm) ⟨x, hx⟩
    (fun h => h0 (congrArg Subtype.val h))

end GlobalTheory.Mem.Df
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDefStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroColumns_classSumForm_posDef : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), SpectralModel.ColsPos (I.cols l) := by
  first | exact @GlobalTheory.Mem.Df.cols_pos | exact GlobalTheory.Mem.Df.cols_pos | (intros; apply GlobalTheory.Mem.Df.cols_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLOneEqDual
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (σ : E →+* E)
    (hσ : ∀ x, σ x = star x) (L : Submodule (𝓞 E) (Fin n → E)) :
    dualL σ (1 : Matrix (Fin n) (Fin n) E) L = Formalism.HermitianLatticesTheory.dual (hStd E n) L := by
  have hmem : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L ↔ ∀ x ∈ L, (∑ k, star (x k) * y k) ∈ (algebraMap (𝓞 E) E).range := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    rfl
  have hset : dualSet σ (1 : Matrix (Fin n) (Fin n) E) L = (Formalism.HermitianLatticesTheory.dual (hStd E n) L : Set _) := by
    ext y
    rw [SetLike.mem_coe, hmem]
    simp only [dualSet, Set.mem_setOf_eq]
    refine forall₂_congr fun x _ => ?_
    have : hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ k, star (x k) * y k := by
      simp [hform, Matrix.one_apply, hσ]
    rw [this]
  unfold dualL
  rw [hset, Submodule.span_eq]

theorem GlobalTheory.Mem.Col2.TC.ldG_eq_dual_hStd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (L : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)), LdG (I.rec7 l Z) i hi L = Formalism.HermitianLatticesTheory.dual (hStd B.host.E (B.R.N i)) L := by
  intro B X I hI hP l Z u a i hi L
  have hG : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  unfold LdG
  rw [hG]
  exact GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual _ (fun x => rfl) L

end
end
