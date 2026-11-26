module

public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)


set_option maxHeartbeats 1000000 in
abbrev phiI (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (Z : Comp (T.Q.Xo j) T.Q.c) :=
  phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w

def CurveHyp (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  SpanW (recPlus h j hj) G.w S ∧ BigAt h j hj hG G ∧ ThAt h j hj hG G g0 ∧ (recPlus h j hj).NonZeroComp wF g0


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem curveInst_of [Fintype (Comp (T.Q.Xo j) T.Q.c)]
    (hinj : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ f : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Z, phiI h j hj hG hT la G Z f = 0) → f = 0)
    (hone : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
        ∀ Z Z', RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z') ≤ Q → Z = Z')
    (hloc : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a)
    (hS1 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)))
    (hH2 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ (e : ℕ) (w' : WeightFamilies.Wt D j) (θ : (recB h.toLawsCore).Cusp j w') (hw : wadd wF w' = wsmul e wL),
        (∀ Z, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0) →
        IsUnit (toOsK (recPlus h j hj) la G.w (u0 (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0 θ hw)))
    (hH3 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ b : ↥(Frac0 (recPlus h j hj) la G.w),
        (b : Lw (recPlus h j hj) la G.w) *
          algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
            (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc wF g0)) = 0 → b = 0) :
    CurveInstSt h j hj := by
  intro _ ka wL wF G la S g0 hSp hBig hTh hNZ
  have hH : CurveHyp h j hj hG ka wL wF G S g0 := ⟨hSp, hBig, hTh, hNZ⟩
  have h1 := LocalUnitReduction.finRed (Kp (recPlus h j hj) la G.N) ↥(Frac0 (recPlus h j hj) la G.w) (Jid (recPlus h j hj) la G.w)
    (Comp (T.Q.Xo j) T.Q.c) (fun Z => RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
    (fun Z => phiI h j hj hG hT la G Z) (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
    (hloc _ _ _ G S g0 la hH) (hS1 _ _ _ G S g0 la hH)
  obtain ⟨e, w', θ, hw, hθ⟩ := hTh
  exact curveModel_of_fr (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0 h1.1 h1.2 θ hw
    (hH2 _ _ _ G S g0 la hH e w' θ hw hθ) (hH3 _ _ _ G S g0 la hH)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def ESecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∃ (k : ℕ) (p q : Rp (xplus X E hM) la G.N),
      p ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧ q ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β p = 0) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β q = 0) ∧
      ∀ ζ, (hw ζ).ev p ≠ 0 ∧ (hw ζ).ev q ≠ 0 ∧
        vV (hw ζ).T.V ((hw ζ).ev p) + vV (hw ζ).T.V ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
          vV (hw ζ).T.V ((hw ζ).ev q)

def LocStructSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∀ g : ↥(Frac0 (xplus X E hM) la G.w),
      (∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w))) →
      ∃ (f d : ↥(Frac0 (xplus X E hM) la G.w)) (hd : ∀ ζ, (hw ζ).toSecPt.lift (d : Lw (xplus X E hM) la G.w) ≠ 0),
        toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w g ∧
        ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
          0 ≤ nval (hw ζ).T.V 1 (evL (fun ζ => (hw ζ).toSecPt) ζ (hdList (fun ζ => (hw ζ).toSecPt) l
            (ιW (fun ζ => (hw ζ).toSecPt) (f : Lw (xplus X E hM) la G.w) *
              ↑(isUnit_of_lift_ne (fun ζ => (hw ζ).toSecPt) hd).unit⁻¹)))

theorem locRing_of {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    (h1 : ESecSt G la) (h2 : LocStructSt G la) : LocRingSt G la :=
  fun y hw g0 hC hg0 => ⟨h1 y hw g0 hC hg0, h2 y hw g0 hC hg0⟩

section Inst

variable {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def ValSepSt {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  ∀ (y : PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)),
    ∃ (Zc : PtsG G la → Comp (T.Q.Xo j) T.Q.c) (ι : ∀ ζ, Om (Zc ζ) →+* (hw ζ).T.Fr),
      (∀ ζ, ∃ a : Om (Zc ζ), vV (hw ζ).T.V (ι ζ a) = 1) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
        evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j) = 0 →
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = 0) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
        ι ζ (evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) =
          ι ζ (evC hG (Zc ζ) ((F' : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
      ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' →
        ∃ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
          nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) -
              (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')))

end Inst

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D}


set_option maxHeartbeats 1000000 in
abbrev OmSK (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) : Type :=
  RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
    Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) (Jid (recPlus h j hj) la G.w)


set_option maxHeartbeats 4000000 in
def qZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c)
    (F : (recB h.toLawsCore).Cusp j wF) : OmSK h j hj hG hT G la Z :=
  Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))
    (lwZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w
      (algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
        (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc wF F))))


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
def algZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) :
    Kp (recPlus h j hj) la G.N →+* OmSK h j hj hG hT G la Z :=
  (Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))).comp
    (algebraMap (Kp (recPlus h j hj) la G.N) (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w))


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
def TieSSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  letI : ∀ Z, Module (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z) := fun Z =>
    (algZ h j hj hG hT G la Z).toModule
  (∃ e : SectionSheafQuotient (recPlus h j hj) la G.w wF ≃ₗ[Kp (recPlus h j hj) la G.N] (∀ Z, OmSK h j hj hG hT G la Z),
    ∀ (F : (recB h.toLawsCore).Cusp j wF) (Z : Comp (T.Q.Xo j) T.Q.c),
      e (resF G la F) Z * qZ h j hj hG hT G la Z g0 = qZ h j hj hG hT G la Z F) ∧
  G.del = ∑ᶠ Z : Comp (T.Q.Xo j) T.Q.c, Module.finrank (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z)





end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CurveInj
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

namespace CurveInj

section Lin

variable {k V M : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup M] [Module k M]

def evDual (φ : Module.Dual k V) : V ⊗[k] M →ₗ[k] M :=
  TensorProduct.lid k M ∘ₗ TensorProduct.map φ LinearMap.id

theorem evDual_tmul (φ : Module.Dual k V) (v : V) (m : M) : evDual φ (v ⊗ₜ[k] m) = φ v • m := by
  simp [evDual]

end Lin

theorem coeff_eq_zero {K Kl K' C : Type*} [Field K] [Field Kl] [Field K'] [Algebra K Kl] [Algebra Kl K']
    [AddCommGroup C] [Module K C] {κ : Type*} [Fintype κ] (b : Module.Basis κ K C)
    {ι : Type*} (Ω : ι → Type*) [∀ Z, AddCommGroup (Ω Z)] [∀ Z, Module K (Ω Z)]
    (ev : ∀ Z, C →ₗ[K] Ω Z) (hev : ∀ F : C, (∀ Z, ev Z F = 0) → F = 0)
    (c : κ → K') (hc : ∀ Z, ∑ i, c i ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ev Z (b i)) = 0) : c = 0 := by
  funext i₀
  refine (Module.forall_dual_apply_eq_zero_iff Kl (c i₀)).1 fun φ => ?_
  refine (Module.forall_dual_apply_eq_zero_iff K (φ (c i₀))).1 fun ψ => ?_
  have hF : (∑ i, ψ (φ (c i)) • b i) = 0 := by
    refine hev _ fun Z => ?_
    have h := congrArg (fun t => evDual (M := Ω Z) ψ (evDual (M := Kl ⊗[K] Ω Z) φ t)) (hc Z)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, evDual_tmul, map_zero, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simpa only [map_smul] using h
  exact Fintype.linearIndependent_iff.1 b.linearIndependent _ hF i₀

section Gen

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {ι : Type} (Ω : ι → Type) [∀ Z, CommRing (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
  (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem vw_inj (u : WeightFamilies.Wt D j) (hinj : ∀ F : B.Cusp j u, (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    {g : Rp X la N} (hg : g ∈ Vw X la N u) (h0 : ∀ Z, rzMap X la N (Ω Z) (gF Z) g = 0) : g = 0 := by
  classical
  let b := Module.finBasis B.KO (B.Cusp j u)
  have hs : Submodule.span B.KO (Set.range b) = ⊤ := b.span_eq
  rw [Vw_eq_span_image X la N u hs, ← Set.range_comp] at hg
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (Kp X la N)).1 hg
  have hc : c = 0 := by
    refine coeff_eq_zero (K := B.KO) (Kl := X.Kl la) (K' := Kp X la N) b Ω
      (fun Z => (gF Z).toLinearMap ∘ₗ X.inc u) (fun F hF => hinj F hF) c fun Z => ?_
    refine (Finset.sum_congr rfl fun i _ => ?_).trans ((map_sum _ _ _).symm.trans (h0 Z))
    rw [map_smul, Function.comp_apply, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  simp [hc]

theorem fraction_zero_injective [Finite ι] {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    (f : ↥(Frac0 X la w)) (hf : ∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) : f = 0 := by
  classical
  cases nonempty_fintype ι
  obtain ⟨k, g, hg, hfg⟩ := (mem_Hfr X la w).1 ((mem_Frac0 X la w).1 f.2)
  have hZ : ∀ Z, ∃ n : ℕ, rzMap X la N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0 ^ n * g) = 0 := by
    intro Z
    have h1 := hf Z
    rw [phiZ_apply, hfg, frac_apply, map_mul, map_pow] at h1
    have hu : IsUnit (lwZ X la N (Ω Z) (gF Z) w (w0inv X la w)) := by
      refine IsUnit.of_mul_eq_one (lwZ X la N (Ω Z) (gF Z) w (algebraMap (Rp X la N) (Lw X la w) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) ?_
      rw [← map_mul, mul_comm, section_mul_inverse_eq_one, map_one]
    rw [(hu.pow k).mul_left_eq_zero, lwZ_alg,
      IsLocalization.map_eq_zero_iff (Submonoid.powers (rzMap X la N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)))] at h1
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := h1
    exact ⟨n, by rw [map_mul, map_pow]; exact hn⟩
  choose n hn using hZ
  have hM : ∀ Z, rzMap X la N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0 ^ (Finset.univ.sup n) * g) = 0 := by
    intro Z
    have hle : n Z ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ Z)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul, hn Z, mul_zero]
  have h0 := vw_inj X la N Ω gF _ (hinj _) (sec_pow_mul_mem X la w 0 (wt0 D j) k (Finset.univ.sup n) hg) hM
  apply Subtype.ext
  show (f : Lw X la w) = 0
  rw [hfg, frac_eq_zero_iff]
  exact ⟨_, h0⟩

end Gen

end CurveInj

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem curveInj [Finite (Comp (T.Q.Xo j) T.Q.c)] (hV : GenValInjSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (f : ↥(Frac0 (recPlus h j hj) la G.w))
    (hf : ∀ Z : Comp (T.Q.Xo j) T.Q.c,
      phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) : f = 0 :=
  CurveInj.fraction_zero_injective (recPlus h j hj) la G.N (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z) G.w
    (fun u F hF => hV u F fun Z => (formsEvR_single j hG hT Z _ _).symm.trans (hF Z)) f hf

end Inst

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j)

include h hj

theorem esec_mem_C {w : WeightFamilies.Wt D j} {f : T.R j} : f ∈ cutR T.C j w ↔ f ∈ T.C j w := by
  rw [cutR_eq T.C hj]

theorem esec_mul_mem {w w' : WeightFamilies.Wt D j} {f g : T.R j} (hf : f ∈ cutR T.C j w) (hg : g ∈ cutR T.C j w') :
    f * g ∈ cutR T.C j (wadd w w') := by
  rw [esec_mem_C h hj] at hf hg ⊢
  exact h.toLawsCore.mul j hj w w' f hf g hg

def esecMul {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w) (F' : (recB h.toLawsCore).Cusp j w') :
    (recB h.toLawsCore).Cusp j (wadd w w') :=
  ⟨(F : T.R j) * (F' : T.R j), esec_mul_mem h hj F.2 F'.2⟩

theorem esecMul_coe {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (F' : (recB h.toLawsCore).Cusp j w') :
    ((esecMul h hj F F' : (recB h.toLawsCore).Cusp j (wadd w w')) : T.R j) = (F : T.R j) * (F' : T.R j) := rfl

theorem esec_inc_mul {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (F' : (recB h.toLawsCore).Cusp j w') :
    (recPJ h j hj).inc (wadd w w') (esecMul h hj F F') = (recPJ h j hj).inc w F * (recPJ h j hj).inc w' F' :=
  (incG_mul deg (cutR T.C j) (deg_wadd w w') F F' (esec_mul_mem h hj F.2 F'.2)).symm

def esecW (wL : WeightFamilies.Wt D j) : ℕ → WeightFamilies.Wt D j
  | 0 => wL
  | n + 1 => wadd wL (esecW wL n)

omit h hj in
theorem esecW_eq (wL : WeightFamilies.Wt D j) (n : ℕ) : esecW wL n = addL (wt0 D j) wL (n + 1) := by
  induction n with
  | zero => exact (add_zero_weight_one_eq wL).symm
  | succ n ih => rw [esecW, ih, wadd_addL]

def esecPow {wL : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j wL) :
    (n : ℕ) → (recB h.toLawsCore).Cusp j (esecW wL n)
  | 0 => F
  | n + 1 => esecMul h hj F (esecPow F n)

theorem esec_inc_pow {wL : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j wL) (n : ℕ) :
    (recPJ h j hj).inc (esecW wL n) (esecPow h hj F n) = (recPJ h j hj).inc wL F ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one]; rfl
  | succ n ih =>
    show (recPJ h j hj).inc (wadd wL (esecW wL n)) (esecMul h hj F (esecPow h hj F n)) = _
    rw [esec_inc_mul, ih, pow_succ' _ (n + 1)]

theorem esec_mem_mulL {wL : WeightFamilies.Wt D j} {a b : ℕ} {f g : T.R j}
    (hf : f ∈ cutR T.C j (addL (wt0 D j) wL a)) (hg : g ∈ cutR T.C j (addL (wt0 D j) wL b)) :
    f * g ∈ cutR T.C j (addL (wt0 D j) wL (a + b)) := by
  have := esec_mul_mem h hj hf hg
  rwa [wadd_addL_addL, zero_weight_add] at this

theorem esec_pow_mem {wL : WeightFamilies.Wt D j} {f : T.R j} (hf : f ∈ cutR T.C j wL) (n : ℕ) :
    f ^ (n + 1) ∈ cutR T.C j (addL (wt0 D j) wL (n + 1)) := by
  induction n with
  | zero => rw [zero_add, pow_one, add_zero_weight_one_eq]; exact hf
  | succ n ih =>
    rw [pow_succ]
    have hf' : f ∈ cutR T.C j (addL (wt0 D j) wL 1) := by rw [add_zero_weight_one_eq]; exact hf
    exact esec_mem_mulL h hj ih hf'

theorem esec_monomial_mem {N : ℕ} {wL : WeightFamilies.Wt D j} (x : Fin N → T.R j) (hx : ∀ i, x i ∈ cutR T.C j wL)
    (α : Fin N →₀ ℕ) :
    α = 0 ∨ (α.prod fun i k => x i ^ k) ∈ cutR T.C j (addL (wt0 D j) wL (α.sum fun _ k => k)) := by
  classical
  induction α using Finsupp.induction with
  | zero => exact Or.inl rfl
  | single_add a b f ha hb ih =>
    right
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.prod_single_index (h := fun i k => x i ^ k) (pow_zero _),
      Finsupp.sum_single_index rfl]
    rcases ih with h0 | hmem
    · subst h0
      simp only [Finsupp.prod_zero_index, Finsupp.sum_zero_index, mul_one, add_zero]
      exact esec_pow_mem h hj (hx a) b
    · exact esec_mem_mulL h hj (esec_pow_mem h hj (hx a) b) hmem

theorem esec_hom_mem {N : ℕ} {wL : WeightFamilies.Wt D j} (x : Fin N → T.R j) (hx : ∀ i, x i ∈ cutR T.C j wL)
    (P : MvPolynomial (Fin N) T.Q.c.F) {k : ℕ} (hP : P.IsHomogeneous (k + 1)) :
    MvPolynomial.aeval x P ∈ cutR T.C j (addL (wt0 D j) wL (k + 1)) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : (α.sum fun _ k => k) = k + 1 := by
    have := hP (MvPolynomial.mem_support_iff.mp hα)
    rw [Finsupp.weight_apply] at this
    simpa using this
  rcases esec_monomial_mem h hj x hx α with h0 | hmem
  · subst h0
    simp at hdeg
  · rwa [hdeg] at hmem

theorem esec_evC_aeval (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    (Z : Comp (T.Q.Xo j) T.Q.c) {N : ℕ} (x : Fin N → T.R j) (P : MvPolynomial (Fin N) T.Q.c.F) :
    evC hG Z (MvPolynomial.aeval x P) = MvPolynomial.aeval (fun i => evC hG Z (x i)) P := by
  rw [← evCAlg_apply hG hT Z]
  exact DFunLike.congr_fun (MvPolynomial.comp_aeval x (evCAlg hG hT Z)) P

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.TieUpR
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def KappaTie (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (f : T.R j), f ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n →
    (evC hG Z f = 0 ↔ ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, rdU (T.U j T.σ₀) f (κ Z) x = 0)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RealPtMain
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D}

theorem mul_ringHom_units_ratio {K : Type} [Field K] {W S R : K} (hW : W ≠ 0) (k : ℕ) :
    W ^ k * R * (W * S)⁻¹ ^ k = R / S ^ k := by
  have h1 : W ^ k * W⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hW, one_pow]
  rw [mul_inv, mul_pow, div_eq_mul_inv, ← inv_pow]
  linear_combination (R * S⁻¹ ^ k) * h1

set_option maxHeartbeats 4000000 in
theorem realPt_of (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hwL : 0 < wL.n) (hPt : PtOfSSt h j hj hG G la) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    (hIF : IntFramesSt (T.Q.Xo j) T.Q.c) (hWt : WtField (T.Q.Xo j) T.Q.c)
    (hMod : ModelAtSt (T.Q.Xo j) T.Q.c la) :
    RealPtNZSt h j hj hG G la hU := by
  have hWD := h.toLawsCore.evalWD j hj
  intro ζ
  haveI hD : IsDVRAt (show Pts (Op (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.N)
      (OsK (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.w) from ζ) :=
    ‹∀ ζ : PtsG G la, IsDVRAt ζ› ζ
  haveI : CharZero (Loc ζ) := loc_charZero hU ζ
  obtain ⟨Tc, ι, hloc, hunr⟩ := complSt_holds (Loc ζ)
  have hι : AddValPres ζ ι := addVal_map_of_unr ι hunr
  let kap : Kp (recPlus h j hj) la G.N →+* Tc.Fr :=
    kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι
  letI instK : Algebra (Kp (recPlus h j hj) la G.N) Tc.Fr := kap.toAlgebra
  let φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] Tc.Fr :=
    { toRingHom := phiAt ζ Tc.Fr ι hU hι, commutes' := fun _ => by rfl }
  obtain ⟨alg, y₀, ⟨Z, ψ, hψ⟩, halg, hs0, hrat⟩ := hPt hwL Tc.Fr φ
  have halg' : alg = kap.comp ((@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _
      (Kp.algKl (recPlus h j hj) la G.N)).comp (algebraMap (recB h.toLawsCore).KO ((recPlus h j hj).Kl la))) :=
    RingHom.ext fun a => halg a
  have ho : OverLa la Tc.V alg (ep (unifO (recPlus h j hj) la G.N) ζ) := by
    rw [halg']
    exact overLa_kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι
  obtain ⟨O, _, β, Y, -, hPI, hB⟩ := hMod
  obtain ⟨b, hb⟩ := hB Tc alg _ ho
  letI := alg.toAlgebra
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF Tc alg Y hPI b hb y₀
  obtain ⟨p, φ', y', hm⟩ := hT Z
  have hm2 : FrMap (ψ.comp φ') y' y₀ := frMap_trans _ _ _ φ' ψ y' (genFr hG Z) y₀ hm hψ
  have hy₀T : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) y₀ :=
    ⟨p, ψ.comp φ', y', hm2⟩
  have hW : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      evI y (F : T.R j) = wchar (ex (T.Q.Dw j) (wtA w) w.n) t * evR (T.Q.Xo j) T.Q.c (F : T.R j) y₀ := fun w F =>
    hWt (wtA w) w.n (F : T.R j) (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)) Tc.Fr t y₀ y.1 hy₀T y.2.1 hbor
  let χ : (recPlus h j hj).Forms →+* Tc.Fr := chiI j y
  let ev : Rp (recPlus h j hj) la G.N →+* Tc.Fr := evRp la G.N kap χ (fun a f => by
    have e := chiI_smul j y a f
    rw [halg a] at e
    exact e)
  have hev_k : ∀ c : Kp (recPlus h j hj) la G.N, ev (algebraMap _ (Rp (recPlus h j hj) la G.N) c) = kap c :=
    evRp_alg la G.N kap χ _
  have hev_inc : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      ev (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc w F)) = evI y (F : T.R j) := by
    intro w F
    exact (evRp_emb la G.N kap χ _ ((recPlus h j hj).inc w F)).trans (chiI_inc j h y w F)
  have hev_sec : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) =
      ∑ k, kap (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k))) *
        evI y ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) := by
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hev_k, hev_inc]
  have hs0' : (∑ k, kap (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k))) *
      evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀) ≠ 0 := hs0
  have hev_s0 : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) = wchar (ex (T.Q.Dw j) (wtA wL) wL.n) t *
      ∑ k, kap (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k))) *
        evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀ := by
    rw [hev_sec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hW wL (G.w k)]
    ring
  have hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0)) :=
    IsUnit.mk0 _ (by rw [hev_s0]; exact mul_ne_zero (wchar_ne_zero _ _) hs0')
  let yV : PtV (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho y trivial () trivial
  let yP : (extAll h j hj).Pt' la := ⟨vAtV yV, yV, rfl⟩
  refine ⟨yP, Tc, ι, hloc, hunr, ev, hu, ?_, ?_, ?_⟩
  · intro w F
    rw [extAll_vAt_inc]
    show vAtV yV (F : T.R j) = _
    exact congrArg (nval Tc.V (ep (unifO (recPlus h j hj) la G.N) ζ)) (hev_inc w F).symm
  · intro x
    obtain ⟨k, ⟨g, hg⟩, rfl⟩ := exists_weightZero_fraction_eq _ _ _ x
    rw [coe_weightZeroFraction, liftEv_frac]
    have key : ∀ (g : Rp (recPlus h j hj) la G.N) (hg : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k))
        (hg' : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k)),
        ev g * (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))⁻¹ ^ k =
          phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr)
            (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨g, hg'⟩)) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg0 =>
        intro hg'
        obtain ⟨F, rfl⟩ := hg0
        have hr := hrat k F
        have hr' : phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr) (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k
            ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ F), hg'⟩)) =
            evR (T.Q.Xo j) T.Q.c ((F : T.R j)) y₀ /
              (∑ k', kap (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k'))) *
                evR (T.Q.Xo j) T.Q.c ((G.w k' : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀) ^ k := hr
        rw [hr', hev_inc, hW, ex_addL, wchar_nsmul, hev_s0]
        exact mul_ringHom_units_ratio (wchar_ne_zero (ex (T.Q.Dw j) (wtA wL) wL.n) t) k
      | zero =>
        intro hg'
        have e0 : fr0 (recPlus h j hj) la G.w k ⟨0, hg'⟩ = 0 := Subtype.ext (by rw [coe_weightZeroFraction]; exact map_zero _)
        rw [e0, map_zero, map_zero, map_zero, zero_mul]
      | add a b ha hb iha ihb =>
        intro hg'
        have e1 : fr0 (recPlus h j hj) la G.w k ⟨a + b, hg'⟩ =
            fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩ + fr0 (recPlus h j hj) la G.w k ⟨b, hb⟩ :=
          Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_add, coe_weightZeroFraction, coe_weightZeroFraction]; exact map_add _ _ _)
        rw [e1, map_add (toOsK (recPlus h j hj) la G.w), map_add (phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr)),
          map_add ev, add_mul, iha ha, ihb hb]
      | smul c a ha iha =>
        intro hg'
        have e1 : fr0 (recPlus h j hj) la G.w k ⟨c • a, hg'⟩ = c • fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩ :=
          Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_smul, coe_weightZeroFraction]; exact map_smul _ _ _)
        rw [e1, map_smul (toOsK (recPlus h j hj) la G.w) c,
          Algebra.smul_def c (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩)),
          map_mul, ← iha ha, Algebra.smul_def c a, map_mul, hev_k, mul_assoc]
        rfl
    exact key g hg hg
  · intro w F hNZ
    rw [show ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = evI y (F : T.R j) from hev_inc w F, hW w F]
    refine mul_ne_zero (wchar_ne_zero _ _) ?_
    have hnat := (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)).1
    rw [evR_eq_of_map hWD hnat y₀ p (ψ.comp φ') y' hm2, AlgHom.comp_apply]
    have h2 : evC hG Z (F : T.R j) = φ' ((F : T.R j) p y') := evR_eq_of_map hWD hnat (genFr hG Z) p φ' y' hm
    rw [← h2]
    exact (map_ne_zero_iff _ ψ.toRingHom.injective).2 (hNZ Z)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.IsAlgebraicOfTrdegEq
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {N : ℕ}


variable (K) in
def HomQ (x : Fin N → L) (f : L) : Prop :=
  ∃ (e : ℕ) (A B : MvPolynomial (Fin N) K), A.IsHomogeneous e ∧ B.IsHomogeneous e ∧
    MvPolynomial.aeval x B ≠ 0 ∧ f = MvPolynomial.aeval x A / MvPolynomial.aeval x B

theorem homQ_mul {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f * g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * A', B * B', hA.mul hA', hB.mul hB', by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_mul, map_mul, div_mul_div_comm]⟩

theorem homQ_add {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f + g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * B' + B * A', B * B', (hA.mul hB').add (hB.mul hA'), hB.mul hB',
    by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_add (f := _), map_mul, map_mul, map_mul, div_add_div _ _ hBx hBx']⟩

theorem homQ_inv {x : Fin N → L} {f : L} (hf : HomQ K x f) : HomQ K x f⁻¹ := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  by_cases hAx : MvPolynomial.aeval x A = 0
  · rw [hAx, zero_div, inv_zero]
    exact ⟨0, 0, 1, MvPolynomial.isHomogeneous_zero _ _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩
  · exact ⟨e, B, A, hB, hA, hAx, by rw [inv_div]⟩

theorem homQ_algebraMap (x : Fin N → L) (c : K) : HomQ K x (algebraMap K L c) :=
  ⟨0, MvPolynomial.C c, 1, MvPolynomial.isHomogeneous_C _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩

theorem homQ_ratio (x : Fin N → L) (m k₀ : Fin N) (hx : x k₀ ≠ 0) : HomQ K x (x m / x k₀) :=
  ⟨1, MvPolynomial.X m, MvPolynomial.X k₀, MvPolynomial.isHomogeneous_X _ _, MvPolynomial.isHomogeneous_X _ _,
    by simpa using hx, by simp⟩


variable (K) in
def homQField (x : Fin N → L) : IntermediateField K L where
  carrier := {f | HomQ K x f}
  mul_mem' := fun ha hb => homQ_mul ha hb
  add_mem' := fun ha hb => homQ_add ha hb
  algebraMap_mem' := homQ_algebraMap x
  inv_mem' := fun _ hf => homQ_inv hf

theorem homQ_of_mem_adjoin (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0) {f : L}
    (hf : f ∈ IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) : HomQ K x f := by
  have hle : IntermediateField.adjoin K (Set.range fun m => x m / x k₀) ≤ homQField K x := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨m, rfl⟩
    exact homQ_ratio x m k₀ hx
  exact hle hf

theorem isAlgebraic_of_trdeg_eq (F : IntermediateField K L) (d : ℕ) (hF : Algebra.trdeg K F = d)
    (hL : Algebra.trdeg K L = d) : Algebra.IsAlgebraic F L := by
  have hs := trdeg_add_eq K F (A := L)
  rw [hF, hL] at hs
  have h0 : Algebra.trdeg F L = 0 := by
    rcases Cardinal.add_eq_left_iff.1 hs with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.2 ((Cardinal.natCast_lt_aleph0 (n := d))))
    · exact h
  exact trdeg_eq_zero_iff.1 h0

theorem exists_homInt (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) L) (a : L) :
    ∃ (k n : ℕ) (P : MvPolynomial (Fin N) K) (cf : ℕ → MvPolynomial (Fin N) K), 0 < k ∧ P.IsHomogeneous k ∧
      MvPolynomial.aeval x P ≠ 0 ∧ (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) ∧
      (MvPolynomial.aeval x P * a) ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval x (cf i) * (MvPolynomial.aeval x P * a) ^ i = 0 := by
  set F := IntermediateField.adjoin K (Set.range fun m => x m / x k₀) with hFdef
  obtain ⟨p, hpm, hp⟩ := ((halg.isAlgebraic a).isIntegral : IsIntegral F a)
  have hq : ∀ i, HomQ K x ((p.coeff i : F) : L) := fun i => homQ_of_mem_adjoin x k₀ hx (p.coeff i).2
  choose e A B hA hB hBx hf using hq
  obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n := ⟨_, rfl⟩
  set P : MvPolynomial (Fin N) K := MvPolynomial.X k₀ * ∏ i ∈ Finset.range n, B i with hPdef
  have hPh : P.IsHomogeneous (1 + ∑ i ∈ Finset.range n, e i) :=
    (MvPolynomial.isHomogeneous_X K k₀).mul (MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => hB i)
  have hPx : MvPolynomial.aeval x P = x k₀ * ∏ i ∈ Finset.range n, MvPolynomial.aeval x (B i) := by
    rw [hPdef, map_mul, MvPolynomial.aeval_X, map_prod]
  have hPx0 : MvPolynomial.aeval x P ≠ 0 := by
    rw [hPx]; exact mul_ne_zero hx (Finset.prod_ne_zero_iff.2 fun i _ => hBx i)
  refine ⟨1 + ∑ i ∈ Finset.range n, e i, n, P,
    fun i => P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i,
    by omega, hPh, hPx0, ?_, ?_⟩
  · intro i hi
    have hS : ∑ j ∈ Finset.range n, e j = e i + ∑ j ∈ (Finset.range n).erase i, e j :=
      (Finset.add_sum_erase _ _ (Finset.mem_range.2 hi)).symm
    have h1 := ((hPh.pow (n - i - 1)).mul ((MvPolynomial.isHomogeneous_X K k₀).mul
      (MvPolynomial.IsHomogeneous.prod ((Finset.range n).erase i) B e fun j _ => hB j))).mul (hA i)
    convert h1 using 1
    obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, hS]
    ring
  · beta_reduce
    have hp' : Polynomial.aeval a p = 0 := by rw [Polynomial.aeval_def]; exact hp
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul, hn] at hp'
    have key : ∀ i ∈ Finset.range n,
        MvPolynomial.aeval x (P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i) *
          (MvPolynomial.aeval x P * a) ^ i = MvPolynomial.aeval x P ^ n * (p.coeff i • a ^ i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have hPi : MvPolynomial.aeval x P = x k₀ * (MvPolynomial.aeval x (B i) *
          ∏ j ∈ (Finset.range n).erase i, MvPolynomial.aeval x (B j)) := by
        rw [hPx, ← Finset.mul_prod_erase _ _ hi]
      have hsm : p.coeff i • a ^ i = MvPolynomial.aeval x (A i) / MvPolynomial.aeval x (B i) * a ^ i := by
        rw [Algebra.smul_def, IntermediateField.algebraMap_apply, hf i]
      obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
      have hpow : MvPolynomial.aeval x P ^ n =
          MvPolynomial.aeval x P ^ t * MvPolynomial.aeval x P * MvPolynomial.aeval x P ^ i := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hsm, hpow]
      simp only [map_mul, map_pow, MvPolynomial.aeval_X, map_prod]
      rw [ht, Nat.add_sub_cancel, hPi]
      field_simp [hBx i]
      ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, mul_pow, ← mul_add, add_comm, hp', mul_zero]

end Alg

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def IntFormSt {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → (recB h.toLawsCore).Cusp j wL) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (k n : ℕ) (cf : ℕ → MvPolynomial (Fin N) T.Q.c.F) (b : Om Z), 0 < k →
    (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) →
    b ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval (fun m => evC hG Z ((w m : (recB h.toLawsCore).Cusp j wL) : T.R j)) (cf i) * b ^ i = 0 →
    ∃ g : (recB h.toLawsCore).Cusp j (wsmul k wL),
      evC hG Z ((g : (recB h.toLawsCore).Cusp j (wsmul k wL)) : T.R j) = b

theorem birSt_of (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (hB2 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧
      Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k =>
        evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) /
          evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j)
    (hint : IntFormSt h j hG G.w) : BIRSt h j hj hG G := by
  intro Z a
  obtain ⟨k₀, hx0, htrF⟩ := hB2 Z
  have halg := isAlgebraic_of_trdeg_eq _ _ htrF (htr Z)
  obtain ⟨k, n, P, cf, hk, hP, hP0, hcf, heq⟩ := exists_homInt (K := T.Q.c.F) _ k₀ hx0 halg a
  obtain ⟨g, hg⟩ := hint Z k n cf _ hk hcf heq
  exact ⟨k, g, P, hP, hP0, by rw [hg, mul_comm]⟩

theorem birSt_of_big (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hBig : BigAt h j hj hG G) (hint : IntFormSt h j hG G.w) :
    BIRSt h j hj hG G :=
  birSt_of h j hj hG htr G hBig.2 hint

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.GenValInjPf
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


theorem evR_of_frMap (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {f : Rul Xo c} (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra c.F S] {p : TRing c.F} {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R}
    {w : FrPt Xo c S} (hy : FrMap φ y w) : evR Xo c f w = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hy⟩
  unfold evR evalAt
  rw [dite_eq_left hT]
  exact hW f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec hy

end Gen

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.TieReadSS
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem holSub_comp_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) (hP : P ∈ holSub X la) (k : Comp) :
    P k ∈ (X k).SS (la k) := by
  have hM := siegelSpaceAlgebra_holds (E := E)
  induction hP using Submodule.span_induction with
  | mem x hx => exact hx k
  | zero => exact (hM r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact (hM r (X k) (la k) (la k) 0).1.2.1 _ hx _ hy
  | smul a x _ hx => exact (hM r (X k) (la k) (la k) 0).1.2.2 a _ hx

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

end Formalism.L2.Pj
end
end
