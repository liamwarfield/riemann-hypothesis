module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.DiffCoprimeP

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem not_le_differentIdeal_of_psiUnr {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl (F := F)) (hu : PsiUnr ψ v) : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
  classical
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)

  have key : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
      Valued.v x ≤ exp (-FractionalIdeal.count F v (codiff F)) := by
    intro x
    set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
    have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
    have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
    have k1 : (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
        ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1 := by
      constructor
      · intro H β hβ
        have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
          apply GlobalTheory.AdelicU.af_ext
          intro u
          by_cases hu : u = v
          · subst hu
            rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
            change β u * x = x * β u
            ring
          · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
        rw [e]
        exact H _ (hβ v)
      · intro H y hy
        have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
          rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
        have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
          by_cases hw : w = v
          · subst hw
            change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
            rw [GlobalTheory.AdelicU.evalV_singleFin_self]
            exact hy
          · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
            rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
            exact zero_mem _)
        rw [e] at this
        exact this
    rw [k1, ← h, mem_adelicIdeal_iff codiff_ne_zero]
    constructor
    · intro H
      have := H v
      rwa [hαv] at this
    · intro H w
      by_cases hw : w = v
      · subst hw
        rw [hαv]
        exact H
      · rw [hαw w hw, map_zero]
        exact zero_le
  set c := FractionalIdeal.count F v (codiff F) with hc

  have hc0 : c ≤ 0 := by
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    omega

  have hc1 : 0 ≤ c := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact exp_ne_zero hπ.symm
    set x : Fv F v := ((π⁻¹ : F) : v.adicCompletion F) with hx
    have hvx : Valued.v x = exp 1 := by
      rw [hx, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ, ← exp_neg, neg_neg]
    have h1 : Valued.v x ≤ exp (-c) := by
      rw [hvx, exp_le_exp]
      omega
    have h2 := (hu x).1 ((key x).2 h1)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvx, ← exp_zero, exp_le_exp] at h2
    omega
  have hc2 : c = 0 := le_antisymm hc0 hc1
  intro hle
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv, ← hc, hc2, neg_zero] at h1
  have h2 := (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 (Ideal.dvd_iff_le.2 hle)
  exact h2 (by exact_mod_cast h1.symm)

end GlobalTheory.DiffCoprimeP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open MeasureTheory
open GlobalTheory.Mem.Isom
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri Rig)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriMove

variable {D : D7}

def rdx {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin m) (Fin n) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix id (finCongr h).symm

def rdi {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin n) (Fin m) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix (finCongr h).symm id

theorem rdx_rdi {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdx (K := K) h * rdi (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

theorem rdi_rdx {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdi (K := K) h * rdx (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

def glMove {K : Type} [CommRing K] {m n : ℕ} (h : m = n) (P : Matrix (Fin n) (Fin m) K) (Q : Matrix (Fin m) (Fin n) K)
    (PQ : P * Q = 1) (QP : Q * P = 1) (x : GL (Fin m) K) : GL (Fin n) K where
  val := HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h)
  inv := HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q
  val_inv := by
    have e1 := rdx_rdi (K := K) h
    have e2 : (x.1 : Matrix (Fin m) (Fin m) K) * x.2 = 1 := x.val_inv
    calc HMul.hMul (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
          (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
        = HMul.hMul (HMul.hMul P (HMul.hMul (HMul.hMul (x.1 : Matrix (Fin m) (Fin m) K) (HMul.hMul (rdx (K := K) h) (rdi (K := K) h))) (x.2 : Matrix (Fin m) (Fin m) K))) Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, e2, Matrix.mul_one, PQ]
  inv_val := by
    have e1 := rdi_rdx (K := K) h
    have e2 : (x.2 : Matrix (Fin m) (Fin m) K) * x.1 = 1 := x.inv_val
    calc HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
          (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
        = HMul.hMul (HMul.hMul (rdi (K := K) h) (HMul.hMul (HMul.hMul (x.2 : Matrix (Fin m) (Fin m) K) (HMul.hMul Q P)) (x.1 : Matrix (Fin m) (Fin m) K))) (rdx (K := K) h) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [QP, Matrix.mul_one, e2, Matrix.mul_one, e1]

variable {S S' T T' : HSp D}

def fP (I : IsoMat S S') : Matrix (Fin S'.rank) (Fin S.rank) (Lev.EAf D) := I.P.map (eToEAf D)

def fQ (I : IsoMat S S') : Matrix (Fin S.rank) (Fin S'.rank) (Lev.EAf D) := I.Q.map (eToEAf D)

theorem fP_fQ (I : IsoMat S S') : fP I * fQ I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.PQ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fQ_fP (I : IsoMat S S') : fQ I * fP I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.QP, Matrix.map_one _ (map_zero _) (map_one _)]

def betaMove (I : IsoMat S S') (β : GL (Fin S.rank) (Lev.EAf D)) : GL (Fin S'.rank) (Lev.EAf D) :=
  glMove I.rank_eq (fP I) (fQ I) (fP_fQ I) (fQ_fP I) β

def latMove (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E) :=
  Λ.map ((Matrix.mulVecLin I.P).restrictScalars (𝓞 D.host.E))

def cartMove (I : IsoMat S S') (τ : D.what₂.Tau) (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * s * I.qT τ

def basMove (I : IsoMat S S') (τ : D.what₂.Tau) (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * B * rdx I.rank_eq

def rigMove (I : IsoMat S S') (r : Rig S) : Rig S' where
  Λ := latMove I r.Λ
  β := betaMove I r.β
  s τ := cartMove I τ (r.s τ)
  B τ := basMove I τ (r.B τ)

def homMap (IS : IsoMat S S') (IT : IsoMat T T') : WO S T ≃+ WO S' T' where
  toFun x := HMul.hMul (HMul.hMul IT.aP x) IS.aQ
  invFun y := HMul.hMul (HMul.hMul IT.aQ y) IS.aP
  left_inv x := by
    show HMul.hMul (HMul.hMul IT.aQ (HMul.hMul (HMul.hMul IT.aP x) IS.aQ)) IS.aP = x
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aQ IT.aP) x) (HMul.hMul IS.aQ IS.aP) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [IT.aQ_aP, IS.aQ_aP, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    show HMul.hMul (HMul.hMul IT.aP (HMul.hMul (HMul.hMul IT.aQ y) IS.aP)) IS.aQ = y
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aP IT.aQ) y) (HMul.hMul IS.aP IS.aQ) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [IT.aP_aQ, IS.aP_aQ, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by
    show HMul.hMul (HMul.hMul IT.aP (x + y)) IS.aQ = HMul.hMul (HMul.hMul IT.aP x) IS.aQ + HMul.hMul (HMul.hMul IT.aP y) IS.aQ
    rw [Matrix.mul_add, Matrix.add_mul]

theorem homMap_apply (IS : IsoMat S S') (IT : IsoMat T T') (x : WO S T) :
    homMap IS IT x = HMul.hMul (HMul.hMul IT.aP x) IS.aQ := rfl

def trH (IS : IsoMat S S') (IT : IsoMat T T') (f : WO S T → ℂ) : WO S' T' → ℂ := fun w => f ((homMap IS IT).symm w)

def trLE (IS : IsoMat S S') (IT : IsoMat T T') : (WO S T → ℂ) ≃ₗ[ℂ] (WO S' T' → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (homMap IS IT).symm.toEquiv

def omH (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ) :=
  (trLE IS IT).conjRingEquiv.toMulEquiv.toMonoidHom.comp (om.comp (IS.kap.symm.toMonoidHom.prodMap IT.kap.symm.toMonoidHom))

theorem omH_apply (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S') (h : GA D T') (f : WO S' T' → ℂ) :
    omH IS IT om (g, h) f = trH IS IT (om (IS.kap.symm g, IT.kap.symm h) (trH IS.symm IT.symm f)) := rfl

def polMove {m n m' n' : ℕ} (hm : m = m') (hn : n = n') :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m' n') ℂ :=
  MvPolynomial.rename fun k => (k.1, finCongr hm k.2.1, finCongr hn k.2.2)

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

def triMove (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) : Tri T₀ A A' WW where
  rA := rigMove IA Y.rA
  rA' := rigMove IA' Y.rA'
  rW := rigMove IW Y.rW
  ω t := omH IA IW (Y.ω t)
  ω' t := omH IA' IW (Y.ω' t)
  vac := trH IA IW Y.vac
  vac' := trH IA' IW Y.vac'
  e := Y.e
  c := Y.c
  f t := trH IA IW (Y.f t)
  f' t := trH IA' IW (Y.f' t)
  m := Y.m.map IA.kap
  fd := IA.kap.symm ⁻¹' Y.fd
  m' := Y.m'.map IA'.kap
  fd' := IA'.kap.symm ⁻¹' Y.fd'

end GlobalTheory.TriMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.LocFin

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem inf_le_cptPart (T K : Subgroup G) (hK : IsCompact (K : Set G)) : T ⊓ K ≤ cptPart T := by
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨hg.1, ?_⟩
  have hzp : (Subgroup.zpowers g : Set G) ⊆ K := (Subgroup.zpowers_le (G := G) (H := K)).2 hg.2
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hzp hK.isClosed)

theorem isCompact_map_conj (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have hc : Continuous fun a : G => x * a * x⁻¹ := by fun_prop
  exact hK.image hc

theorem isOpen_map_conj (K : Subgroup G) (hK : IsOpen (K : Set G)) (x : G) :
    IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  exact (Homeomorph.mulLeft x |>.trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK

theorem relIndex_ne_zero_of_isOpen (A H : Subgroup G) (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G)) :
    A.relIndex H ≠ 0 := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have ho : IsOpen ((A.subgroupOf H : Subgroup H) : Set H) := hA.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_cptPart_ne_zero (T A H : Subgroup G) (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G))
    (hTH : cptPart T ≤ H) : (T ⊓ A).relIndex (cptPart T) ≠ 0 := by
  have hPT : cptPart T ≤ T := by
    rw [cptPart, Subgroup.closure_le]; exact fun t ht => ht.1
  have e : (T ⊓ A) ⊓ cptPart T = A ⊓ cptPart T := by
    ext g; simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hPT h.2, h.1⟩, h.2⟩⟩
  rw [← Subgroup.inf_relIndex_right, e, Subgroup.inf_relIndex_right]
  have h1 := relIndex_ne_zero_of_isOpen A H hA hH
  have : (A.subgroupOf H).FiniteIndex := ⟨h1⟩
  have : Finite (cptPart T ⧸ A.subgroupOf (cptPart T)) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE A hTH).injective
  exact Subgroup.index_ne_zero_of_finite

theorem finite_of_subset_mul (T K' : Subgroup G) (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

end Generic

section Main

theorem hKT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := GlobalTheory.T.continuous_involutive_local_transpose_inverse

theorem hKPa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := GlobalTheory.T.orbit_compact_mod_centralizer_separable_local

theorem hKA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := GlobalTheory.T.exists_compact_ge_compactPart_twistedCentralizer

theorem hKPb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := GlobalTheory.T.normCommuting_twistedConj_compact_mem_twistedCentralizer_mul

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twConj (hU : Unr E) (n : ℕ) (w : Pl E) (x y : GLw n w) :
    nrmL n w (x⁻¹ * y * thL n w x) = x⁻¹ * nrmL n w y * x := by
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    simp only [nrmL, if_pos hs, h1, MonoidHom.id_apply]
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have h2 := (hKT E hU n w).2
    rw [h1] at h2
    simp only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]
    group

theorem continuous_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun u => u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have hc := (hKT E hU n w).1
    rw [h1] at hc
    have e : nrmL n w = fun u => u * thetaGL n (cj w) u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id.mul hc

theorem proper (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (C : Set (GLw n w)) (hC : IsCompact C) : ∃ D : Set (GLw n w), IsCompact D ∧
      ∀ x : GLw n w, x⁻¹ * y * thL n w x ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, x = t * d := by
  have hθ := (hKT E hU n w).1
  obtain ⟨D₁, hD₁, h₁⟩ := hKPa E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL hU n w))
  set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)
  have hC₂ : IsCompact C₂ := (hD₁.prod (hC.prod hD₁)).image (by fun_prop)
  obtain ⟨D₂, hD₂, h₂⟩ := hKPb E hU n w y hy C₂ hC₂
  refine ⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩
  intro x hx
  obtain ⟨z, hz, d, hd, rfl⟩ := h₁ x ⟨_, hx, by rw [nrmL_twConj hU]⟩
  have hz2 : z⁻¹ * y * thL n w z ∈ C₂ := ⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by
    simp only [map_mul]; group⟩
  obtain ⟨t, ht, d₂, hd₂, rfl⟩ := h₂ z hz hz2
  exact ⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ K' : Subgroup (GLw n w), IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) K' → (∀ x : GLw n w, twCent (thL n w) y ⊓ (GlobalTheory.LFun.KGL w (n := n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (thL n w) y) ∧ (twCent (thL n w) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (thL n w) y)) ≠ 0) ∧ ∀ C : Set (GLw n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (thL n w) y : Set (GLw n w)) (K' : Set (GLw n w)) | (Quotient.out q)⁻¹ * y * thL n w (Quotient.out q) ∈ C}.Finite := by
  intro E _ _ _ hU n w y hy K' hK'
  obtain ⟨hK'o, hK'K, -⟩ := hK'
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  obtain ⟨H, hH, hPH⟩ := hKA E hU n w y hy
  refine ⟨fun x => ⟨inf_le_cptPart _ _ (isCompact_map_conj _ hKc x),
    relIndex_cptPart_ne_zero _ _ H (isOpen_map_conj _ hK'o x) hH hPH⟩, fun C hC => ?_⟩
  obtain ⟨D, hD, hP⟩ := proper hU n w y hy C hC
  exact finite_of_subset_mul _ K' hK'o D hD _ hP

end Main

end GlobalTheory.LocFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFinitenessStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularTwistedOrbit_local_finiteness : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ K' : Subgroup (GLw n w), IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) K' → (∀ x : GLw n w, twCent (thL n w) y ⊓ (GlobalTheory.LFun.KGL w (n := n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (thL n w) y) ∧ (twCent (thL n w) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (thL n w) y)) ≠ 0) ∧ ∀ C : Set (GLw n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (thL n w) y : Set (GLw n w)) (K' : Set (GLw n w)) | (Quotient.out q)⁻¹ * y * thL n w (Quotient.out q) ∈ C}.Finite := by
  first | exact @GlobalTheory.LocFin.main | exact GlobalTheory.LocFin.main | (intros; apply GlobalTheory.LocFin.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbNormalises
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Norm

section Abstract

variable {A : Type} [CommRing A] {n r d : ℕ} {X Y : Matrix (Fin n) (Fin r) A} {L K : Matrix (Fin r) (Fin n) A}
  (e : Fin d → Fin r) (P Q : Matrix (Fin d) (Fin d) A)

theorem row_span {Z : Matrix (Fin r) (Fin n) A} {I : Set (Fin r)} {a : Fin r} (hz : ∀ i ∈ I, (Z * X) a i = 0)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : (Z *ᵥ y) a = 0 := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.ker (LinearMap.proj a ∘ₗ Z.mulVecLin) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact hz i hi
  exact this hy

theorem blk_mulVec (y : Fin n → A) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y =
      y + X.submatrix id e *ᵥ (P *ᵥ fun a => (K *ᵥ y) (e a)) + Y.submatrix id e *ᵥ (Q *ᵥ fun a => (L *ᵥ y) (e a)) := by
  rw [add_mulVec, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rfl

theorem blk_span (hLX : L * X = 0) (hKX : K * X = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y ∈
      Submodule.span A ((fun i => Xᵀ i) '' I) := by
  have h1 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i _ => by rw [hLX]; rfl) hy
  rw [blk_mulVec, h1, mulVec_zero, mulVec_zero, add_zero]
  refine add_mem hy ?_
  rcases hI with hI | hI
  · rw [mulVec_eq_sum]
    refine sum_mem fun a _ => ?_
    rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e a, hI a, rfl⟩)
  · have h2 : (fun a => (K *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i hi => by
      rw [hKX, Matrix.one_apply_ne]; rintro rfl; exact hI a hi) hy
    rw [h2, mulVec_zero, mulVec_zero]
    exact zero_mem _

theorem blk_perp (hLX : L * X = 0) (hLY : L * Y = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : ∀ i ∈ I, (L *ᵥ y) i = 0) : ∀ i ∈ I,
    (L *ᵥ ((1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y)) i = 0 := by
  intro i hi
  have h1 : L * X.submatrix id e = 0 := by
    ext a b
    exact congrFun (congrFun hLX a) (e b)
  rw [blk_mulVec, mulVec_add, mulVec_add, mulVec_mulVec _ L (X.submatrix id e), h1, zero_mulVec, add_zero,
    Pi.add_apply, hy i hi, zero_add]
  rcases hI with hI | hI
  · have h2 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => hy _ (hI a)
    rw [h2, mulVec_zero, mulVec_zero, mulVec_zero]
    rfl
  · rw [mulVec_mulVec _ L]
    change ∑ a, (L * Y.submatrix id e) i a * _ = 0
    refine Finset.sum_eq_zero fun a _ => ?_
    have : (L * Y.submatrix id e) i a = 0 := by
      change (L * Y) i (e a) = 0
      rw [hLY, Matrix.one_apply_ne]
      rintro rfl
      exact hI a hi
    rw [this, zero_mul]

end Abstract

open GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}


omit [NumberField E] in
theorem conj_mem_trivOn {A B B' : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {m u : GAd σ J}
    (h1 : ∀ y ∈ A, (matHom _ σ J m).1 *ᵥ y ∈ A) (h2 : ∀ y ∈ A, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A)
    (h3 : ∀ y ∈ B, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ B') (hu : u ∈ trivOn σ J A B') : m * u * m⁻¹ ∈ trivOn σ J A B := by
  have e : ∀ (a : GAd σ J) y, (matHom _ σ J a⁻¹).1 *ᵥ (matHom _ σ J a).1 *ᵥ y = y := fun a y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  have e' : ∀ y, (matHom _ σ J m).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y = y := fun y => by
    simpa only [inv_inv] using e m⁻¹ y
  have i1 : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A := fun y => ⟨h1 y, fun h => e m y ▸ h2 _ h⟩
  have i2 : ∀ y, y ∈ A ↔ (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A := fun y => ⟨h2 y, fun h => e' y ▸ h1 _ h⟩
  have v : ∀ y, (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := fun y => by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, mulVec_mulVec, mulVec_mulVec]
  refine ⟨fun y => by rw [v, ← i1, ← hu.1, ← i2], fun y hy => ?_⟩
  have := h1 _ (hu.2 _ (h3 y hy))
  rwa [mulVec_sub, e', ← v] at this


omit [NumberField E] in
theorem mem_trivOn_span {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {u : GAd σ J} {T : Set (Fin r)} {j : Fin r}
    (hj : j ∈ T) (hu : ∀ i ∈ T, u ∈ trivOn σ J A (colSpan F X {i})) : u ∈ trivOn σ J A (colSpan F X T) := by
  refine ⟨(hu j hj).1, fun y hy => ?_⟩
  have : colSpan F X T ≤ A.comap ((matHom _ σ J u).1.mulVecLin - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact (hu i hi).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
  exact this hy

theorem blockEmb_normalises : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      (∀ g, ∀ u ∈ GlobalTheory.StdPar.unip σ J Xf S, ι g * u * (ι g)⁻¹ ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
      ∀ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E), ι (GlobalTheory.CuspRep.infGL E d y) ∈ infPts σ J := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, _, _, _, hΦ, hι⟩ hS _ _
  constructor
  · let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
    have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
        adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
    have hLX : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
      rw [hm, hW.xx]; exact Matrix.map_zero _ (map_zero _)
    have hLY : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
      rw [hm, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
      rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have sp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colSpan F X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colSpan F X I := fun g I hI y hy => by
      rw [hι]
      exact blk_span (Y := adMat F Y) e _ _ hLX hKX hI hy
    have pp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colPerp σ J X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colPerp σ J X I := fun g I hI y hy => by
      rw [hι]
      simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      exact blk_perp (X := adMat F X) (K := adMat F (cT (σ : E →+* E) Y * J)) e _ _ hLX hLY hI hy
    have cp : ∀ p : Fin r → Prop, (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k ∧ p k} := fun p => by
      by_contra hc
      obtain ⟨h1, h2⟩ := not_or.1 hc
      obtain ⟨b, k, hk, hb, hp⟩ : ∃ b, e b ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k} := by simpa only [not_forall, not_not] using h2
      refine h1 fun a => ⟨k, hk, ?_, hp⟩
      have hb' : l + b.val ≤ k.val := hb
      have : ¬ k.val + 1 < l + d := fun h' => hS k (by omega) h' hk
      change l + a.val ≤ k.val
      omega
    have cp' : (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k} := by
      simpa only [and_true] using cp fun _ => True
    intro g u hu
    refine ⟨Subgroup.mem_iInf.2 fun j => ?_, conj_mem_trivOn (sp g cp') (map_inv ι g ▸ sp g⁻¹ cp')
      (map_inv ι g ▸ pp g⁻¹ cp') hu.2⟩
    have hu1 := Subgroup.mem_iInf.1 hu.1
    by_cases hj : j ∈ Set.range e
    · refine conj_mem_trivOn (B' := colSpan F X (Set.range e)) (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (fun y hy => map_inv ι g ▸ sp g⁻¹ (I := Set.range e) (Or.inl fun a => Set.mem_range_self a) y
          (Submodule.span_mono (Set.image_mono (Set.singleton_subset_iff.2 hj)) hy)) (mem_trivOn_span hj ?_)
      obtain ⟨b, rfl⟩ := hj
      rintro _ ⟨a, rfl⟩
      have key : ∀ a b : Fin d, ∀ k ∈ S, k < e a → k < e b := fun a b k hk hka => by
        have h1 : k.val < l + a.val := hka
        have h2 : ¬ l ≤ k.val := fun h' => hS k h' (by omega) hk
        change k.val < l + b.val
        omega
      have : {i | ∃ k ∈ S, i ≤ k ∧ k < e b} = {i | ∃ k ∈ S, i ≤ k ∧ k < e a} := Set.ext fun i =>
        ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩, fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩⟩
      rw [this]
      exact hu1 _
    · exact conj_mem_trivOn (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (map_inv ι g ▸ sp g⁻¹ (I := {j}) (Or.inr fun a (ha : e a = j) => hj (Exists.intro a ha))) (hu1 j)
  · have k1 : ∀ z, GlobalTheory.LFun.finTens F E (Φ.symm z) = (GlobalTheory.LFun.finAdEquiv F E).symm (GlobalTheory.CuspRep.pFin E z) := fun z => by
      have := congrArg (GlobalTheory.CuspRep.pFin E) (hΦ (Φ.symm z))
      rw [RingEquiv.apply_symm_apply] at this
      rw [this]
      exact ((GlobalTheory.LFun.finAdEquiv F E).symm_apply_apply _).symm
    have k2 : ∀ y, ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) = 1 := fun y => by
      have := congrArg Units.val (GlobalTheory.CuspRep.pFin_infGL (E := E) y)
      have e : ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) =
          ((GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E)).map (GlobalTheory.LFun.finAdEquiv F E).symm :=
        Matrix.ext fun a b => k1 _
      rw [e, show (GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E) = 1 from this]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have k3 : ∀ x, sigR (Af F) σ (GlobalTheory.LFun.finTens F E x) = GlobalTheory.LFun.finTens F E (sigR (AF F) σ x) := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a b => rfl
    intro y
    refine Units.ext ?_
    change (matHom _ σ J (ι (GlobalTheory.CuspRep.infGL E d y))).1.map (GlobalTheory.LFun.finTens F E) = 1
    have o : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) (AF F ⊗[F] E)).map (GlobalTheory.LFun.finTens F E) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [hι, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), k2,
      ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ (sigR (Af F) σ) _ k3, ← map_inv, k2, o, o, Formalism.UG.cT_one, sub_self]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

end GlobalTheory.BlockForms.Norm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SelfDualFirstProj

variable {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

instance charZero_Fv : CharZero (Fv F v) :=
  (RingHom.charZero_iff (algebraMap F (Fv F v)).injective).1 inferInstance

theorem isOpen_integers : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) :=
  Valued.isOpen_valuationSubring _

theorem exists_nat_mem (c : Fv F v) (hc : c ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ c⁻¹ * (n : Fv F v) ∈ v.adicCompletionIntegers F := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let O := v.adicCompletionIntegers F
  let S : AddSubgroup (Fv F v) := (O.toSubring.toAddSubgroup).comap (AddMonoidHom.mulLeft c⁻¹)
  let H : AddSubgroup O := S.comap (O.toSubring.subtype.toAddMonoidHom)
  have hS : IsOpen (S : Set (Fv F v)) :=
    (isOpen_integers v).preimage (continuous_const.mul continuous_id)
  have hH : IsOpen (H : Set O) := hS.preimage continuous_subtype_val
  let H' : OpenAddSubgroup O := ⟨H, hH⟩
  have : Finite (O ⧸ H) := AddSubgroup.instFiniteQuotientOfSeparatelyContinuousAddOfCompactSpace H'
  have hne : H.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  refine ⟨H.index, Nat.pos_of_ne_zero hne, ?_⟩
  have hm := H.nsmul_index_mem (1 : O)
  simpa [H, S] using hm

theorem exists_finite_residues (n : ℕ) (hn : 0 < n) :
    ∃ R : Set (Fv F v), R.Finite ∧ ∀ y ∈ v.adicCompletionIntegers F,
      ∃ r ∈ R, ∃ u ∈ v.adicCompletionIntegers F, y = r + (n : Fv F v) * u := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let U : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hUo : IsOpen U := isOpen_integers v
  have hUc : IsCompact U := isCompact_iff_compactSpace.mpr inferInstance
  have hc : (n : Fv F v) ≠ 0 := by exact_mod_cast hn.ne'
  let V : U → Set (Fv F v) := fun x => (fun y => (y - (x : Fv F v)) * (n : Fv F v)⁻¹) ⁻¹' U
  have hVo : ∀ x, IsOpen (V x) := fun x =>
    hUo.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  have hcov : U ⊆ ⋃ x, V x := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    show (y - y) * (n : Fv F v)⁻¹ ∈ U
    rw [sub_self, zero_mul]
    exact (v.adicCompletionIntegers F).zero_mem
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover V hVo hcov
  refine ⟨(fun x : U => (x : Fv F v)) '' (t : Set U), (t.finite_toSet).image _, ?_⟩
  intro y hy
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hxt, hyx⟩ := this
  refine ⟨x, ⟨x, hxt, rfl⟩, (y - (x : Fv F v)) * (n : Fv F v)⁻¹, hyx, ?_⟩
  field_simp
  ring

theorem exists_finite_residues_pi {κ : Type} [Fintype κ] (n : ℕ) (hn : 0 < n) :
    ∃ R : Set (κ → Fv F v), R.Finite ∧ ∀ t : κ → Fv F v, (∀ i, t i ∈ v.adicCompletionIntegers F) →
      ∃ r ∈ R, ∃ u : κ → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ t = r + n • u := by
  obtain ⟨R, hR, h⟩ := exists_finite_residues v n hn
  haveI := hR.to_subtype
  refine ⟨Set.range (fun f : κ → R => fun i => (f i : Fv F v)), Set.finite_range _, ?_⟩
  intro t ht
  choose r hr u hu hru using fun i => h (t i) (ht i)
  refine ⟨fun i => r i, ⟨fun i => ⟨r i, hr i⟩, rfl⟩, u, hu, ?_⟩
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
  exact hru i

theorem exists_pair_of_annihilator : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    [DecidableEq κ] (ψk : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψk (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  intro F _ _ v κ _ _ ψk Λ c hc hψ hself hbd η hη
  let O := v.adicCompletionIntegers F
  have ψ1 : ∀ x : Fv F v, x ∈ O → ψk x = 1 := fun x hx => by
    simpa using (hψ x).2 hx 1 O.one_mem
  have dotO : ∀ u w : κ → Fv F v, (∀ i, u i ∈ O) → (∀ i, w i ∈ O) → u ⬝ᵥ w ∈ O := by
    intro u w hu hw
    exact O.toSubring.sum_mem fun i _ => O.toSubring.mul_mem (hu i) (hw i)
  let L₀ : AddSubgroup (κ → Fv F v) := AddSubgroup.pi Set.univ (fun _ => O.toSubring.toAddSubgroup)
  have hL₀ : ∀ x, x ∈ L₀ ↔ ∀ i, x i ∈ O := fun x => by
    simp [L₀, AddSubgroup.mem_pi]
  let P : AddSubgroup (κ → Fv F v) := Λ.map (AddMonoidHom.fst _ _)
  have hP : ∀ x, x ∈ P ↔ ∃ y, (x, y) ∈ Λ := fun x => by
    simp only [P, AddSubgroup.mem_map, AddMonoidHom.coe_fst]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l.2, hl⟩
    · rintro ⟨y, hy⟩; exact ⟨(x, y), hy, rfl⟩

  have LB : ∀ u₁ u₂ : κ → Fv F v, (∀ i, u₁ i ∈ O) → (∀ i, u₂ i ∈ O) → (c • u₁, c • u₂) ∈ Λ := by
    intro u₁ u₂ h₁ h₂
    refine (hself _).2 fun l hl => ψ1 _ ?_
    have e1 : (c • u₁) ⬝ᵥ l.2 = u₁ ⬝ᵥ (c • l.2) := by rw [smul_dotProduct, dotProduct_smul]
    have e2 : l.1 ⬝ᵥ (c • u₂) = (c • l.1) ⬝ᵥ u₂ := by rw [smul_dotProduct, dotProduct_smul]
    simp only
    rw [e1, e2]
    exact O.toSubring.sub_mem (dotO _ _ h₁ fun i => (hbd l hl i).2) (dotO _ _ (fun i => (hbd l hl i).1) h₂)
  have hsingle : ∀ i (t : Fv F v), t ∈ O → ∀ j, (Pi.single i t : κ → Fv F v) j ∈ O := by
    intro i t ht j
    by_cases h : j = i
    · subst h; simpa using ht
    · simp [Pi.single_apply, h, O.zero_mem]

  have hcη : ∀ i, c * η i ∈ O := by
    intro i
    refine (hψ _).1 fun t ht => ?_
    have hb : ((0 : κ → Fv F v), c • Pi.single i t) ∈ Λ := by
      have := LB 0 (Pi.single i t) (fun _ => O.zero_mem) (hsingle i t ht)
      simpa using this
    have := hη _ hb
    rwa [dotProduct_smul, dotProduct_single, smul_eq_mul, ← mul_assoc] at this
  obtain ⟨N, hN, hNc⟩ := GlobalTheory.SelfDualFirstProj.exists_nat_mem v c hc
  have hNeq : ∀ z : Fv F v, (N : Fv F v) * z = (c⁻¹ * N) * (c * z) := fun z => by
    field_simp
  have bich : GlobalTheory.PlaceModel.IsBichar (fun x y : κ → Fv F v => ψk (x ⬝ᵥ y)) :=
    ⟨fun a b y => by simp only [add_dotProduct, AddChar.map_add_eq_mul],
     fun a y z => by simp only [dotProduct_add, AddChar.map_add_eq_mul],
     fun y => by simp, fun a => by simp⟩
  have hmem : η ∈ P := by
    refine GlobalTheory.DualTransfer.mem_of_double_annihilator (fun x y => ψk (x ⬝ᵥ y)) bich ⊤ ⊤ L₀ L₀ P
      le_top le_top le_top ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ N hN ?_ ?_ η trivial ?_ ?_
    · intro u hu y hy
      exact ψ1 _ (dotO _ _ ((hL₀ u).1 hu) ((hL₀ y).1 hy))
    · intro x _ h
      refine (hL₀ x).2 fun i => (hψ _).1 fun t ht => ?_
      have := h (Pi.single i t) ((hL₀ _).2 (hsingle i t ht))
      rwa [dotProduct_single] at this
    · intro y _ h
      refine (hL₀ y).2 fun i => (hψ _).1 fun t ht => ?_
      have := h (Pi.single i t) ((hL₀ _).2 (hsingle i t ht))
      rwa [single_dotProduct, mul_comm] at this
    · intro k hk x _
      refine ⟨((k : Fv F v)⁻¹) • x, trivial, ?_⟩
      have hk0 : (k : Fv F v) ≠ 0 := by exact_mod_cast hk.ne'
      rw [← Nat.cast_smul_eq_nsmul (Fv F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    · intro k hk x _
      refine ⟨((k : Fv F v)⁻¹) • x, trivial, ?_⟩
      have hk0 : (k : Fv F v) ≠ 0 := by exact_mod_cast hk.ne'
      rw [← Nat.cast_smul_eq_nsmul (Fv F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    · intro k hk t t' h
      have hk0 : (k : Fv F v) ≠ 0 := by exact_mod_cast hk.ne'
      funext i
      have := congrFun h i
      simp only [Pi.smul_apply, nsmul_eq_mul] at this
      exact mul_left_cancel₀ hk0 this
    · intro k hk
      obtain ⟨R, hR, h⟩ := GlobalTheory.SelfDualFirstProj.exists_finite_residues_pi (κ := κ) v k hk
      exact ⟨R, hR, fun t ht => by
        obtain ⟨r, hr, u, hu, e⟩ := h t ((hL₀ t).1 ht)
        exact ⟨r, hr, u, (hL₀ u).2 hu, e⟩⟩
    · intro k hk
      obtain ⟨R, hR, h⟩ := GlobalTheory.SelfDualFirstProj.exists_finite_residues_pi (κ := κ) v k hk
      exact ⟨R, hR, fun t ht => by
        obtain ⟨r, hr, u, hu, e⟩ := h t ((hL₀ t).1 ht)
        exact ⟨r, hr, u, (hL₀ u).2 hu, e⟩⟩
    · intro u hu
      have hu' := (hL₀ u).1 hu
      refine (hP _).2 ⟨c • (0 : κ → Fv F v), ?_⟩
      have := LB ((c⁻¹ * N) • u) 0 (fun i => O.toSubring.mul_mem hNc (hu' i)) (fun _ => O.zero_mem)
      convert this using 2
      rw [smul_smul, ← Nat.cast_smul_eq_nsmul (Fv F v)]
      congr 1
      field_simp
    · intro u hu
      obtain ⟨y, hy⟩ := (hP u).1 hu
      refine (hL₀ _).2 fun i => ?_
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hNeq]
      exact O.toSubring.mul_mem hNc (hbd _ hy i).1
    · refine (hL₀ _).2 fun i => ?_
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hNeq]
      exact O.toSubring.mul_mem hNc (hcη i)
    · intro y _ h
      refine hη y ((hself _).2 fun l hl => ?_)
      simp only [zero_dotProduct, zero_sub, AddChar.map_neg_eq_inv]
      rw [h l.1 ((hP _).2 ⟨l.2, hl⟩), inv_one]
  obtain ⟨y, hy⟩ := (hP η).1 hmem
  exact ⟨y, hy⟩

end GlobalTheory.SelfDualFirstProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLocalSubgroup_firstProj_eq_annihilator : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    [DecidableEq κ] (ψk : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψk (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  first | exact @GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator | exact GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator | (intros; apply GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

variable {F : Type} [Field F] [NumberField F]

def IsSelfDualFor {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (ν : Measure (Fv F v)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∀ f ∈ SB (Fv F v), ∫ y, (∫ x, f x * χ (x * y) ∂ν) ∂ν = f 0

open Classical in
def measV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) : Measure (Fv F v) :=
  if h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν then h.choose else 0

def fourV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) {κ : Type} [Fintype κ] (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) : ℂ :=
  ∫ x, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) ∂(Measure.pi fun _ : κ => measV ψ v)


open Classical in
variable (F) in
def measI (κ : Type) [Fintype κ] : Measure (κ → mixedEmbedding.mixedSpace F) :=
  Measure.pi fun _ : κ => (Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ)).prod
    (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ))

def eInf {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ))

end GlobalTheory.WeylFour

end
end
