module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
public import Formalism.LocalToGlobal.JointCharacters.SameChr

@[expose] public section

section -- merged from Formalism.LocalToGlobal.BesselHermitianTheta.BesselUnipotentSubgroup
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsDualFlag {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (f : Matrix (Fin B.rank) (Fin d.ρ) D.host.E) :
    Prop where
  iso : IsIsoSub B f
  pair : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * B.gram * f = 1
  perpA : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram * f = 0
  perpZ : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) f * B.gram).mulVec d.z = 0

end Formalism.L2.Theta

end
end

section -- merged from Formalism.LocalToGlobal.NumberFieldFamilies.ThetaC
section -- merged from Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCP
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.Inhab Formalism.BasicNotions.Examples₂

variable {D : D7}

theorem xs_fits (R : Ranks) (t j : ℕ) (hj : j < R.m) : R.k + j * (t + 1) ≤ R.r + j * t - (R.m - j) / 2 := by
  have h1 : j * (t + 1) = j * t + j := by ring
  rw [h1]
  generalize j * t = s
  unfold Ranks.r
  omega

theorem nu_le (R : Ranks) (t j : ℕ) : (R.m - j) / 2 ≤ R.r + j * t := by
  have hk := R.m_add_three_le_k
  have : (R.m - j) / 2 ≤ R.r := by unfold Ranks.r; omega
  omega

def sigTow (D : D7) (t : ℕ) : Tow D t where
  Xs := fun j => posSpace star_isIntegral (D.R.k + j * (t + 1))
  Xs_rank := fun _ _ => rfl
  Xs_sig := fun _ _ => ⟨posSpace_sigOK _ _, fun _ => Or.inl rfl⟩
  Ys := fun j => dSpace star_isIntegral (D.R.r + j * t) ((D.R.m - j) / 2)
  Ys_rank := fun _ _ => rfl
  Ys_sig := fun j _ => dSpace_sigOK _ _ _ (nu_le D.R t j)
  iXYs := fun _ => extLE _ _
  iXYs_isom := fun j hj x y => extLE_isom _ _ ((xs_fits D.R t j hj).trans (Nat.sub_le _ _)) _ _
    (fun i => negTail_false _ _ _ (lt_of_lt_of_le i.isLt (xs_fits D.R t j hj))) x y
  iYXm := extLE _ _
  iYXm_isom := fun x y => extLE_isom _ _ (by
      have := D.R.two_le_m
      unfold Ranks.r
      rw [Nat.mul_succ]
      omega) _ _ (fun i => (negTail_false _ _ _ (by have := i.isLt; omega)).symm) x y


open Classical in
def towC (D : D7) (t : ℕ) : Tow D t := if h : t = D.R.t then h ▸ recTow D else sigTow D t

def SpSig (D : D7) : Prop :=
  ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef ∧
    ∀ τ, (D.sp.Y j).sig τ = (D.R.r + j * D.R.t - (D.R.m - j) / 2, (D.R.m - j) / 2)


open Classical in
def lowC (V : HSp D) (i : ℕ) : HSp D :=
  if i = 0 then V else if h : ∃ V' : HSp D, IsWittLower V V' i then fixSig h.choose else V

def EmbU (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ g g' h, EmbRel A B ι g h → EmbRel A B ι g' h → g = g'

def EmbRat (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ γ ∈ GQ B, ∃ γ' ∈ GQ A, EmbRel A B ι γ' γ

def TopInt (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ s : GA D B → GA D A, (∀ h, EmbRel A B ι (s h) h) →
  ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
  ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFunSm (th0 D) A φ → IsAutFunSm (th0 D) B F → IsCuspFun B F →
    IntegrableOn (fun h => star (φ (s h)) * F h) 𝓕 μ


section Bessel

variable (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)

def NPair (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain (NFlagQ B d.e) p.2 p.1 ∧ p.1 p.2 = 1

def besIn (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) (F : GA D B → ℂ) (x : GA D B) : ℂ :=
  ∫ n in p.2, F ((n : GA D B) * x) * star (besChar ψ d (n : GA D B)) ∂p.1

end Bessel

def BesInt1 (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  ∀ p, NPair d p → ∀ F : GA D B → ℂ, IsAutFun B F → ∀ x,
    IntegrableOn (fun n : NFlag B d.e => F ((n : GA D B) * x) * star (besChar ψ d (n : GA D B))) p.2 p.1

def BesInv (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  ∀ p p', NPair d p → NPair d p' → ∀ F : GA D B → ℂ, IsAutFun B F →
    ∀ γ' ∈ GQ B, ∀ γ : GA D A, EmbRel B A ι γ' γ → ∀ x, besIn ψ d p F (γ' * x) = besIn ψ d p' F x

def BesInt2 (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  HSpace.IsIsomEmb A B ι → ∀ p, NPair d p → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
  ∀ (μ : Measure (GA D A)) (𝓕 : Set (GA D A)), μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ →
  ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFunSm (th0 D) A φ → IsCuspFun A φ → IsAutFunSm (th0 D) B F → IsCuspFun B F →
    IntegrableOn (fun h => star (φ h) * besIn ψ d p F (s h * (d.y : GA D B))) 𝓕 μ

structure PerGaps (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  embU : EmbU D
  embRat : EmbRat D
  topInt : TopInt D
  int1 : BesInt1 ψ
  inv : BesInv ψ
  int2 : BesInt2 ψ

section Bessel2

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}


end Bessel2

end Formalism.L2.Fam.ThC

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.Inhab

variable {D : D7}

structure ChrIn (D : D7) where
  chr : D.what₂.Tup → ℕ → chrA D
  chr_exp : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (chr μ (j.1 + 1)).1 τ (-(D.hc τ).e j)
  chr_res : ∀ μ j, 1 ≤ j → j ≤ D.R.m → ResEta D (chr μ j).1 0
  eta : chrA D
  eta_exp : ∀ τ, HasInfExp D eta.1 τ (1 / 2)
  eta_res : ResEta D eta.1 1
  eta_unr : UnramEverywhere D eta.1

abbrev lowY (D : D7) (t j i : ℕ) : HSp D := lowC ((towC D t).Ys j) i

structure Free {ψ : AddChar (AF D.host.F) ℂ} (_Om : WeilC ψ) : Type 1 where
  petF : HSp D → ℝ
  petF_pos : ∀ V, 0 < petF V
  fact : ∀ V W, Set (schC ψ V W)
  conjS : ∀ V W, schC ψ V W → schC ψ V W
  conjS_add : ∀ V W Φ Φ', conjS V W (Φ + Φ') = conjS V W Φ + conjS V W Φ'
  conjS_smul : ∀ V W (c : ℂ) Φ, conjS V W (c • Φ) = star c • conjS V W Φ
  conjS_conjS : ∀ V W Φ, conjS V W (conjS V W Φ) = Φ
  conjS_fact : ∀ V W, ∀ Φ ∈ fact V W, conjS V W Φ ∈ fact V W
  conjS_kfin : ∀ V W, ∀ Φ ∈ kfinC ψ V W, conjS V W Φ ∈ kfinC ψ V W

  PosE : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type
  FJd : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type
  [fjAdd : ∀ A B ι, AddCommGroup (FJd A B ι)]
  [fjMod : ∀ A B ι, Module ℂ (FJd A B ι)]
  BE : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), PosE A B ι → FJd A B ι → afC D A → cuspC D B → ℂ
  BE_right : ∀ A B ι p s φ, IsLinearMap ℂ (BE A B ι p s φ)
  BE_add : ∀ A B ι p s φ φ' F, BE A B ι p s (φ + φ') F = BE A B ι p s φ F + BE A B ι p s φ' F
  BE_smul : ∀ A B ι p s (c : ℂ) φ F, BE A B ι p s (c • φ) F = star c * BE A B ι p s φ F
  pos1 : D.what₂.Word → {d : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) // (d.y : GA D (D.sp.Y 0)) = 1}
  posSym : D.what₂.Word → {d : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) // (d.y : GA D (D.sp.Y 0)) = 1}

  f1 : ∀ u, Matrix (Fin (D.sp.Y 0).rank) (Fin (pos1 u).1.ρ) D.host.E
  free_flag_dual : ∀ u, IsDualFlag (pos1 u).1 (f1 u)
  colAF : ∀ (u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), D.what₂.Mu u →ₗ[ℂ] cuspC D (D.sp.X j)
  PhiX : ∀ (_u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), schC ψ (D.sp.X j) (D.sp.X (j + 1))
  rowAF : ∀ (μ : D.what₂.Tup) (j : ℕ), D.what₂.Mult μ j →ₗ[ℂ] cuspC D (D.sp.Y j)
  PhiY : ∀ (_μ : D.what₂.Tup) (j : ℕ), schC ψ (D.sp.Y (j + 1)) (D.sp.Y j)
  PhiYLow : ∀ (_μ : D.what₂.Tup) (j i : ℕ), schC ψ (D.sp.Y (j + 1)) (lowY D D.R.t j i)
  PhiYupLow : ∀ (_μ : D.what₂.Tup) (j i : ℕ), schC ψ (D.sp.Y j) (lowY D D.R.t (j + 1) i)
  mY : D.what₂.Tup → ℕ → ℝ
  mY_pos : ∀ μ j, 0 < mY μ j
  adelicDataRowMeasureScale_trivialTuple : ∀ j, mY D.what₂.mu0 j = 1
  mY_zero : ∀ μ, mY μ 0 = 1

attribute [instance] Free.fjAdd Free.fjMod

variable {ψ : AddChar (AF D.host.F) ℂ}

section Ties

variable (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ) (c : ChrIn D) (f : Free Om)

end Ties

end Formalism.L2.Fam.ThC

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Host Formalism.L2.JoinChr Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

variable {D : D7}

def plE (τ : D.what₂.Tau) : InfinitePlace D.host.E := InfinitePlace.mk (tauE D τ)


open Classical in
def embAt (τ : D.what₂.Tau) : (plE τ).Completion →+* ℂ :=
  if (plE τ).embedding = tauE D τ then InfinitePlace.Completion.extensionEmbedding (plE τ)
  else (starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding (plE τ))

theorem conj_tauE_ne (τ τ' : D.what₂.Tau) : ComplexEmbedding.conjugate (tauE D τ) ≠ tauE D τ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, tauE_sqrtMinusD, tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have := sqrt_d_pos D
  linarith

theorem plE_bij (D : D7) : Function.Bijective (plE (D := D)) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with e | e
    · exact tauE_inj e
    · exact absurd e (conj_tauE_ne τ τ')
  · intro w
    obtain ⟨τ, h | h⟩ := tauE_or w.embedding
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_embedding]⟩
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]⟩

theorem plE_complex (τ : D.what₂.Tau) : (plE τ).IsComplex := by
  rw [plE, InfinitePlace.isComplex_mk_iff]
  exact fun h => conj_tauE_ne τ τ h

structure AdBC (D : D7) where
  Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E
  cont : Continuous Φ
  cont' : Continuous Φ.symm
  inc : ∀ k : D.host.E, Φ (incA D k) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) k

  fin : ∀ x, finPart D x = 1 ↔ (Φ x).2 = 1

  inf : ∀ τ x, embAt τ ((Φ x).1 (plE τ)) = cmpAt D τ x

  idem : ∀ P e, IsPlIdem D e P ↔ Φ e = pairA D.host.E 0 (singleV D.host.E P 1)

  int : ∀ x, finPart D x ∈ intAE D ↔ ∀ P, (Φ x).2 P ∈ P.adicCompletionIntegers D.host.E

  idemF : ∀ v, (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).1 = 0 ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), (P.under (𝓞 D.host.F) = v →
      (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).2 P = 1) ∧
      (P.under (𝓞 D.host.F) ≠ v → (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).2 P = 0)

namespace AdBC

variable (B : AdBC D)

def up : (AE D)ˣ →* Ideles D.host.E := Units.map B.Φ.toMonoidHom

def dn : Ideles D.host.E →* (AE D)ˣ := Units.map B.Φ.symm.toMonoidHom

theorem dn_up (x : (AE D)ˣ) : B.dn (B.up x) = x := Units.ext (by simp [up, dn])

theorem up_inc (k : D.host.Eˣ) : B.up (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k := Units.ext (by simp [up, B.inc]; rfl)

theorem toUnits_cont : Continuous Circle.toUnits := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_subtype_val.comp (continuous_inv : Continuous fun z : Circle => z⁻¹)

def toH : chrA D →* HChar D.host.E where
  toFun χ := ⟨(Circle.toUnits.comp χ.1).comp B.dn,
    (toUnits_cont.comp χ.2.1.1).comp (Continuous.units_map _ B.cont'), fun k => by
      rw [← B.up_inc, MonoidHom.comp_apply, B.dn_up, MonoidHom.comp_apply, χ.2.1.2, map_one]⟩
  map_one' := Subtype.ext (MonoidHom.ext fun _ => map_one Circle.toUnits)
  map_mul' _ _ := Subtype.ext (MonoidHom.ext fun _ => map_mul Circle.toUnits _ _)

end AdBC

section Dens

variable {L : Type} [Field L] [NumberField L]

end Dens

namespace AdBC

variable (B : AdBC D)

def ResTriv : Prop := ∀ χ : HChar D.host.E, χ.TrivOn D.host.F → ∀ a, χ.1 (B.up (idF D a)) = 1

def EtaIs : Prop := ∀ χ : chrA D, (B.toH χ).ResEta D.host.F → IsEta D (χ.1.comp (idF D))

def UnrAll : Prop := ∀ χ : chrA D, (∀ v, (B.toH χ).UnrAt v) → UnramEverywhere D χ.1

end AdBC

def EtaU (D : D7) : Prop := ∀ η η', IsEta D η → IsEta D η' → η = η'

structure ChrGaps (B : AdBC D) : Prop where
  triv : B.ResTriv
  etaIs : B.EtaIs
  unr : B.UnrAll
  etaU : EtaU D

section Frame

variable {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

variable (B : AdBC D)

variable {ψ : AddChar (AF D.host.F) ℂ} (Gc : ChrGaps B) (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ)
  (f : Free Om)

end Frame

end Formalism.L2.Fam.ThC

end
