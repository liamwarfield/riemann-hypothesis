module

public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.CutPassage3
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.NearConstantMultiplicities
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

structure CxPassIn3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (C CH : ℝ)
    (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) : Prop where

  ratMuP : X.RATmu (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false

  isGood : Formalism.IndefR.TransferLatticeStatement.IsGood τ

  chars : Formalism.IndefR.CxPass.CharsX τ A3.A.fam.X

  m1 : Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩

  nbarPos : 0 < nbar

  near_constant_multiplicities : Formalism.IndefR.CxPass.NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de

  laTie : ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G

section Pass3

variable [_root_.NumberField.IsTotallyComplex K] {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {X : CxData A3.fam3.amb3} {s : ℕ} {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH} {C CH : ℝ}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)} {cf : ConvFace A3.fam3.base3}
  {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
  [∀ s, FiniteDimensional K (Ws s)] {τ : ∀ s, Representation K G (Ws s)} {nbar : ℝ}

theorem passage3_of (hN : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf)
    (hP : CxPassIn3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH S Ws τ nbar) :
    Passage ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true) :=
  Formalism.IndefR.CxPass.cutPassage3S K G Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S Ws τ nbar hN.ok hN.sep
    hN.stable hN.inBlock hN.h4pos (hN.pos false) (hN.pos true) (fun b => (hN.what₂ b).1) hN.ratMu hN.h2P hP.ratMuP
    hN.gUnit hN.gEquiv hN.npTie.1 hN.npTie.2 hP.isGood hP.chars hP.m1 hP.nbarPos hP.near_constant_multiplicities hP.laTie

def packageFullHecke (hN : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf)
    (hP : CxPassIn3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH S Ws τ nbar) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH :=
  basePackageFullHecke { toPrimitiveStatementsBaseLiftsOnly := hN, passage := passage3_of hN hP }

end Pass3

end Formalism.IndefR.Cx
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section End3

open Formalism.IndefR.Cx Formalism.L2.Geo Formalism.MainNotions

variable [_root_.NumberField.IsTotallyComplex D.what₂.LL] {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def PassIn3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (C CH : ℝ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module D.what₂.LL (Ws s))
    (_ : ∀ s, FiniteDimensional D.what₂.LL (Ws s)) (τ : ∀ s, Representation D.what₂.LL G (Ws s)) (nbar : ℝ),
    CxPassIn3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) C CH S Ws τ nbar

def primitivePackageFullHecke {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (H : HkDat3 A3) (C CH : ℝ) (hC : R.WeakCharacterisation F)
    (hP : CovolumeOntoIsometryConditions R F sEE H C CH) (hI : PassIn3 R F C CH) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (R.convOf F H) C CH :=
  letI := hI.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  packageFullHecke (base_lifts_package_of_primitive_links hOk hsep hC hP) hI.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

def primRows3 {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    (hP : PrimRows3 R F) : IndefRows (lv (F.fc (R.toCx3 F).zs) false) :=
  indefiniteDataAtBaseLevel (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP)

theorem primRows3_data {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) : (primRows3 hOk hsep R F hC hP).toIndefData = (R.toCx3 F).data F.cr false := rfl

end End3

end Formalism.IndefR.Links

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

section Pieces

variable (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
  (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
  (t : GA D (D.sp.Y 0)) (c : ℝ) (v₀ : M.Vec)

def SquareIntegrableTransfer : Prop :=
  ∀ F : GA D (D.sp.Y 0) → ℂ, Continuous F → (∀ γ ∈ GQ (D.sp.Y 0), ∀ x, F (γ * x) = F x) →
    MemLp F 2 (μ.restrict 𝓕) →
      MemLp (fun x => F (ι.symm x * t)) 2 (muX X) ∧
        ∫ x, ‖F (ι.symm x * t)‖ ^ 2 ∂(muX X) = c * ∫ x in 𝓕, ‖F x‖ ^ 2 ∂μ

def RphFix : Prop :=
  ∀ T ∈ E, ∀ hF : MemLp (fun x => ev M v₀ T (ι.symm x * t)) 2 (muX X),
    X.Rph (star (hF.toLp _)) = star (hF.toLp _)

def EvalIntoT : Prop :=
  ∀ T ∈ E, ∃ F : EEC X G, ((F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x * t)) ∧
    ‖(F : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 T T).re

def EvalOntoT : Prop :=
  ∀ F : EEC X G, ∃ T ∈ E, (F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x * t)

def EvalInjT : Prop :=
  ∀ T ∈ E, ((fun x => ev M v₀ T (ι.symm x * t)) =ᵐ[muX X] 0) → T = 0

end Pieces

theorem evalTieT_of (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
    (t : GA D (D.sp.Y 0)) (c : ℝ) (v₀ : M.Vec) (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1)
    (hI : EvalIntoT M μ 𝓕 E X G ι t c v₀) (hO : EvalOntoT M E X G ι t v₀) (hJ : EvalInjT M E X ι t v₀) :
    EvalTieT M μ 𝓕 E X G ι t c := by
  classical
  choose Φ hΦ using fun T : E => hI T T.2
  have key : ∀ (T : E) (F : EEC X G), ((F : L2X X) =ᵐ[muX X] fun x => ev M v₀ (T : MMap M) (ι.symm x * t)) →
      Φ T = F := by
    intro T F hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ T).1.trans hF.symm
  let L : E →ₗ[ℂ] EEC X G :=
    { toFun := Φ
      map_add' := fun T T' => by
        apply key
        have h1 := (hΦ T).1
        have h2 := (hΦ T').1
        have h3 := Lp.coeFn_add ((Φ T : EEC X G) : L2X X) ((Φ T' : EEC X G) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a T => by
        rw [RingHom.id_apply]
        apply key
        have h1 := (hΦ T).1
        have h3 := Lp.coeFn_smul a ((Φ T : EEC X G) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hinj : Function.Injective L := by
    intro T T' h
    have hd : L (T - T') = 0 := by rw [map_sub, h, sub_self]
    have h1 := (hΦ (T - T')).1
    have h0 : ((fun x => ev M v₀ ((T - T' : E) : MMap M) (ι.symm x * t)) =ᵐ[muX X] 0) := by
      have hz : ((Φ (T - T') : EEC X G) : L2X X) = 0 := by
        have : Φ (T - T') = 0 := hd
        rw [this]; rfl
      have := Lp.coeFn_zero ℂ 2 (muX X)
      rw [← hz] at this
      exact h1.symm.trans this
    have := hJ ((T - T' : E) : MMap M) (T - T').2 h0
    exact sub_eq_zero.mp (Subtype.ext this)
  have hsurj : Function.Surjective L := by
    intro F
    obtain ⟨T, hT, hF⟩ := hO F
    exact ⟨⟨T, hT⟩, key ⟨T, hT⟩ F hF⟩
  exact ⟨v₀, hv, LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun T => hΦ T⟩

section Assembly

variable {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
  {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA}
  {t : GA D (D.sp.Y 0)} {c : ℝ} {v₀ : M.Vec}

theorem norm_sq_toLp {f : X.B.I.GA → ℂ} (hf : MemLp f 2 (muX X)) :
    ‖(hf.toLp f : L2X X)‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(muX X) := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  have h1 : (fun a => ⟪(hf.toLp f : L2X X) a, (hf.toLp f : L2X X) a⟫_ℂ) =
      fun a => (((‖(hf.toLp f : L2X X) a‖ ^ 2 : ℝ)) : ℂ) := by
    funext a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h1, integral_complex_ofReal]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha]

theorem re_ipM_eq {T : MMap M} (hT : ∃ c', IsMultIP M μ 𝓕 T T c') (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) :
    (ipM M μ 𝓕 T T).re = ∫ x in 𝓕, ‖T v₀ x‖ ^ 2 ∂μ := by
  unfold ipM
  rw [dite_eq_left hT]
  obtain ⟨-, heq⟩ := hT.choose_spec v₀ v₀
  have hprod : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    simp
  rw [hprod, mul_one] at heq
  rw [← heq]
  have hpt : ∀ g, star (T v₀ g) * T v₀ g = ((‖T v₀ g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  simp_rw [hpt]
  rw [integral_complex_ofReal]
  simp

end Assembly

end Formalism.IndefR.AutomorphicEvaluation

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.CoreTExist
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.CoreT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Half

variable (P : Formalism.L2.Host.PiBar D.host)


variable (hF : OFull D) (hz : OZeta D) (hN : N1ab)

end Half

section Chr

theorem mem_of_latHat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) {x : Fin n → E}
    (h : (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E))) : x ∈ Λ := by
  have key : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)),
      (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (y i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hs : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩)
      have hv : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
          Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := Submodule.subset_span ⟨x, hx, rfl⟩
      convert Submodule.smul_mem _ (⟨(1 : E) ⊗ₜ[F] a, hs⟩ : Formalism.L2.Herm.intAf F E) hv using 1
      funext i
      show Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (a ⊗ₜ[F] x i) =
        ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rfl
    | zero =>
      convert Submodule.zero_mem (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ) using 1
      funext i
      exact map_zero _
    | add y z _ _ hy hz =>
      convert add_mem hy hz using 1
      funext i
      exact map_add _ _ _
    | neg y _ hy =>
      convert neg_mem hy using 1
      funext i
      exact map_neg _ _
  have hg : x ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
      (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
    exact key _ h
  rwa [Formalism.UG.P.global_lattice_one_holds F E (Fin n) Λ hfin hsp] at hg

end Chr

section Unif

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}



variable {U : Unf Xo c σ r} {V : HSp D} {dict : GA D V → Σ k, Frame (U.X k).Ψ r} {mu : GA D V → ℂ}

end Unif

section Core

variable (Q : Par D)

variable {Q}

end Core

section Rec

variable (Q : Par D)



variable {Q}

end Rec

section Pg

end Pg

section Rows

section Gen

variable {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (s : E →ₐ[F] E)
  (hs : ∀ e, ∃ f : F, algebraMap F E f = e + s e)

include hs

end Gen

section H90

end H90

end Rows

section Cover

open CategoryTheory

attribute [local instance] Over.cartesianMonoidalCategory

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

end Cover

section IdMap

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

section Cech

variable {X Y : Scheme.{0}}

variable (L : LB X)

variable {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)


end Cech

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}


end IdMap

section Trans

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

include hle

end Trans

section Lat

variable {n : ℕ}

end Lat

section OM

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}



variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec)
  (c' : Coeff T.Q.l) (jL : D.what₂.LL →+* c'.F) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)

variable {T R i v₀ c' jL lev}

end OM

end Formalism.IndefR.CoreT
end
end
