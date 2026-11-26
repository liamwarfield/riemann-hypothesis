module

public import Formalism.LocalToGlobal.Columns.CoefCol
public import Formalism.LocalToGlobal.HermitianForms.FormsTied

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.TiedCF
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

section Step

variable (D : ColRec)

def sigD : D.host.E →ₐ[D.host.F] D.host.E := letI := D.host.cmStar; D.sp.cm.sig

def embT : D.what₂.Tau → D.host.E →+* ℂ := fun τ => D.host.emb (D.eTau τ : D.R.GG)

theorem rankN (i : ℕ) (hi : i ≤ D.R.m) : letI := D.host.cmStar; (D.sp.X i).rank = D.R.N i :=
  letI := D.host.cmStar; D.sp.X_rank i hi

def gramN (i : ℕ) (hi : i ≤ D.R.m) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E :=
  letI := D.host.cmStar
  (D.sp.X i).gram.reindex (finCongr (rankN D i hi)) (finCongr (rankN D i hi))

def clsCrd (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.clsLat u i c).map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def selfDualLatticeCoords (i : ℕ) (hi : i ≤ D.R.m) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.sp.X i).L0.map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def badG : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | (D.host.g 0 : 𝓞 D.host.F) ∈ v.asIdeal ∨ (D.host.g 1 : 𝓞 D.host.F) ∈ v.asIdeal}

abbrev PlT (u : D.what₂.Word) : Type :=
  {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

variable {D}

def lamT (u : D.what₂.Word) (i : ℕ) : D.what₂.Tau → DomWeight (D.R.N i) :=
  fun τ => shW ((D.fm u).lam i τ) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)


set_option maxHeartbeats 1000000 in
structure ClsTied (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) where

  lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) (D.mem u).A.T D.R.f (badG D)

  y : (D.mem u).C.cls i → UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  y_lat : ∀ c (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (clsCrd D u i hi c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb

  stabI : ∀ c, (D.mem u).C.stab i c →* UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom


end Step

section AtT

variable {D : ColRec}

structure AtTTied (u : D.what₂.Word) where

  eV : (D.mem u).A.vT ≃ PlT D u

  piU : 𝓞 D.host.E
  piU_K : (piU : D.host.E) ∈ D.host.K
  piU_norm : (piU : D.host.E) * D.host.conj piU = ((D.mem u).A.T : D.host.E)
  piU_cong : piU - 1 ∈ Ideal.span
    {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}

  res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v
  res_surj : ∀ v, Function.Surjective (res v)
  res_pi : ∀ v, res v piU = 0

  res_conj : ∀ v (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj piU → res v pb ≠ 0
  res_v : ∀ v (x : 𝓞 D.host.F), x ∈ (eV v).1.asIdeal ↔ res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = 0

  tauOf : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ v (x : 𝓞 D.host.F),
    x ∈ (eV v).1.asIdeal ↔ (0 : WithTop ℤ) < D.what₂.places.val w
      (D.embE (D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
        (algebraMap (𝓞 D.host.F) D.host.E x)))

  seenP : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ τ : D.what₂.Tau,
    (0 : WithTop ℤ) < D.what₂.places.val w (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG)
      (if (D.fm u).seenP w = true then (piU : D.host.E) else D.host.conj piU)))

def AtTTied.Pv {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) : Ideal (𝓞 D.host.E) := RingHom.ker (A.res v)

abbrev Ld (D : ColRec) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  dualL (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)

abbrev Lk {u : D.what₂.Word} (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  clsCrd D u i hi c ⊔ A.Pv v • Ld D u i hi c


set_option maxHeartbeats 1000000 in
structure LvTied (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) where

  pr : ∀ v c, ↥(Ld D u i hi c) →+ (D.fm u).lv i v c
  pr_surj : ∀ v c, Function.Surjective (pr v c)
  pr_smul : ∀ v c (a : 𝓞 D.host.E) z, pr v c (a • z) = A.res v a • pr v c z
  pr_ker : ∀ v c z, pr v c z = 0 ↔ z.1 ∈ A.Pv v • Ld D u i hi c

  fv_ker : ∀ v c z, (D.fm u).fv i v c (pr v c z) = 0 ↔ z.1 ∈ Lk A i hi v c

  prk : ∀ v c, ↥(Lk A i hi v c) →+ (D.fm u).lk i v c
  prk_surj : ∀ v c, Function.Surjective (prk v c)
  prk_smul : ∀ v c (a : 𝓞 D.host.E) z, prk v c (a • z) = A.res v a • prk v c z
  prk_ker : ∀ v c z, prk v c z = 0 ↔ z.1 ∈ A.Pv v • Lk A i hi v c

  te : ∀ v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c (pr v c z) = 1 →
    ∀ h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ Lk A i hi v c, prk v c ⟨_, h⟩ = (D.fm u).te i v c

variable {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m}




end AtT

end Formalism.L2.Col.CF

end
end

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

section XP

variable (D : ColRec)

theorem rankP : letI := D.host.cmStar; D.sp.X'.rank = D.R.N D.R.m - 1 := by
  letI := D.host.cmStar
  have h := D.sp.X'_rank
  have h2 := D.R.m_add_three_le_k
  rw [h]; unfold Ranks.rankX' Ranks.r Ranks.N; rw [Nat.mul_add, Nat.mul_one]; omega

def gramP : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E :=
  letI := D.host.cmStar
  D.sp.X'.gram.reindex (finCongr (rankP D)) (finCongr (rankP D))

def iXc : (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E) :=
  letI := D.host.cmStar
  ((((D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm) :
      (D.sp.X D.R.m).V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E)) :
      (D.sp.X D.R.m).V →ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E)).comp D.sp.iX').comp
    ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm :
      (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] D.sp.X'.V)

def zc : Fin (D.R.N D.R.m) → D.host.E :=
  letI := D.host.cmStar
  ((D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm)) D.sp.z

def iXm : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) D.host.E := LinearMap.toMatrix' (iXc D)

def IsExt (z0 : Fin (D.R.N D.R.m) → D.host.E) {R : Type} [CommRing R] (φ : D.host.E →+* R)
    (g' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R)
    (g : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R) : Prop :=
  g * (iXm D).map φ = (iXm D).map φ * g' ∧ g *ᵥ (fun a => φ (z0 a)) = fun a => φ (z0 a)

variable {D}


set_option maxHeartbeats 1000000 in
structure ClsPTied (u : D.what₂.Word) where

  lev : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f (badG D)
  y : (D.fm u).clsP → UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  lat : (D.fm u).clsP → Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)
  y_lat : ∀ c (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb
  lat_fin : ∀ c, Module.Finite (𝓞 D.host.E) (lat c)
  stabI : ∀ c, (D.fm u).stabilizer₂ c →* UJ (sigD D : D.host.E →+* D.host.E) (gramP D)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

def sgT (u : D.what₂.Word) : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => shW ((D.fm u).sg τ) ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)



set_option maxHeartbeats 1000000 in
structure TilTied (u : D.what₂.Word) (A : AtTTied u) (K : ClsPTied u) (P : LvTied u A D.R.m le_rfl) where
  z0 : Fin (D.R.N D.R.m) → D.host.E
  lastCoordinateUniformizerVector_spans_orthogonal_line : ∃ a : D.host.E, z0 = a • zc D
  hermitianForm_lastCoordinateUniformizerVector_self : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 z0 = ((D.mem u).A.T : D.host.E)
  ga : (D.fm u).clsP → UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
  til_lat : ∀ c, mulLat (ga c).1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) =
    (K.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}
  til_fv : ∀ v c (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c))) (r : 𝓞 D.host.E),
    (r : D.host.E) = hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 ((ga c).1.1 *ᵥ x.1) →
    (D.fm u).fv D.R.m v ((D.fm u).til c) (P.pr v _ x) = A.res v r




set_option maxHeartbeats 4000000 in
structure TilAd {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    (Tl : TilTied u A K P) (Km : ClsTied u D.R.m le_rfl) where
  ka : (D.fm u).clsP → Km.lev.U
  til_ad : ∀ c (g : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsExt D Tl.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K.y c).1.1 g.1 →
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tl.ga c).1 * (Km.y ((D.fm u).til c)).1 =
      g * (ka c).1


end XP

section All

variable {D : ColRec}



end All

end Formalism.L2.Col.CF

end
