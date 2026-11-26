module

public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.WLeWjOne
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.CloudFilling.ExistsPowOrbRep
noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.G

section Generic

variable {G : Type} [Group G] [Finite G] [OrbSec G] (z : G)

def orbOf (g : G) : Fin (nOrb z) := (orbEquiv z).symm (QuotientGroup.mk g)

theorem orbOf_mul_pow (g : G) (i : ℕ) : orbOf z (g * z ^ i) = orbOf z g := by
  unfold orbOf
  congr 1
  rw [QuotientGroup.eq]
  have : (g * z ^ i)⁻¹ * g = (z ^ i)⁻¹ := by group
  rw [this]
  exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers z i)

theorem orbOf_orbRep (v : Fin (nOrb z)) : orbOf z (orbRep z v) = v := by
  unfold orbOf
  rw [orbRep_mk]
  exact (orbEquiv z).symm_apply_apply v

theorem orbOf_posG (v : Fin (nOrb z)) (s : Fin (orderOf z)) : orbOf z (posG z ⟨v, s⟩) = v := by
  rw [posG_apply, orbOf_mul_pow, orbOf_orbRep]

theorem exists_pow_orbRep (g : G) : ∃ i : ℕ, i < orderOf z ∧ orbRep z (orbOf z g) * z ^ i = g := by
  obtain ⟨⟨v, s⟩, hx⟩ := (posG z).surjective g
  refine ⟨s, s.isLt, ?_⟩
  rw [← hx, orbOf_posG]
  exact (posG_apply z v s).symm

end Generic

def tau1P (φ : Formalism.HC.Frame) (t : φ.A) : φ.Psi := ⟨φ.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩

abbrev zH (φ : Formalism.HC.Frame) (h : φ.A) : φ.Psi := zPsi φ (φ.iota h)

theorem tau1P_injective' (φ : Formalism.HC.Frame) : Function.Injective (tau1P φ) := by
  intro t t' h
  have h1 := congrArg (fun x : φ.Psi => ((x : φ.GG)).2) h
  simpa [tau1P, Formalism.HC.Frame.tau1, Formalism.HC.Frame.iota] using h1

theorem tau_add_nsmul (φ : Formalism.HC.Frame) (t h : φ.A) (i : ℕ) : tau1P φ (t + i • h) = tau1P φ t * zH φ h ^ i := by
  apply Subtype.ext
  have e1 : φ.iota (t + i • h) = φ.iota t * φ.iota h ^ i := by
    rw [← iotaH_nsmul]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  show (((1 : _), (1 : _)), φ.iota (t + i • h)) = (((1 : _), (1 : _)), φ.iota t) * (((1 : _), (1 : _)), φ.iota h) ^ i
  rw [e1]
  simp [Prod.pow_mk]

theorem orderOf_zH (φ : Formalism.HC.Frame) (h : φ.A) : orderOf (zH φ h) = addOrderOf h := by
  show orderOf (zPsi φ (φ.iota h)) = addOrderOf h
  rw [orderOf_zPsi]
  exact orderOf_ofAdd_eq_addOrderOf h

def vOfH (φ : Formalism.HC.Frame) (h t : φ.A) : Fin (nOrb (zH φ h)) := orbOf (zH φ h) (tau1P φ t)

def bsH (φ : Formalism.HC.Frame) (h t : φ.A) : φ.A :=
  φ.iotaInv ((orbRep (zH φ h) (vOfH φ h t) : φ.Psi) : φ.GG).2

private theorem orbRep_vOfH_eq_secPsi_tau1P (φ : Formalism.HC.Frame) (h t : φ.A) :
    orbRep (zH φ h) (vOfH φ h t) = secPsi φ (zH φ h) (tau1P φ t) := by
  have hv : (QuotientGroup.mk (tau1P φ t) : φ.Psi ⧸ Subgroup.zpowers (zH φ h)) =
      orbEquiv (zH φ h) (vOfH φ h t) :=
    ((orbEquiv (zH φ h)).apply_symm_apply _).symm
  have hz : ((zH φ h : φ.Psi) : φ.GG).1 = 1 := rfl
  have hs : OrbSec.sec (zH φ h) (tau1P φ t) = secPsi φ (zH φ h) (tau1P φ t) := if_pos hz
  rw [orbRep_of_mk _ _ _ hv, hs]

theorem bsH_eq_bsA (φ : Formalism.HC.Frame) (h t : φ.A) : bsH φ h t = Formalism.MainNotions.Inhab.bsA h t := by
  unfold bsH
  rw [orbRep_vOfH_eq_secPsi_tau1P]
  rfl

theorem vOfH_add_nsmul (φ : Formalism.HC.Frame) (h t : φ.A) (i : ℕ) : vOfH φ h (t + i • h) = vOfH φ h t := by
  unfold vOfH
  rw [tau_add_nsmul, orbOf_mul_pow]

theorem orbRep_vOfH (φ : Formalism.HC.Frame) (h t : φ.A) : orbRep (zH φ h) (vOfH φ h t) = tau1P φ (bsH φ h t) := by
  rw [orbRep_vOfH_eq_secPsi_tau1P, bsH_eq_bsA]
  exact Subtype.ext rfl

theorem bsH_orb' (φ : Formalism.HC.Frame) (h t : φ.A) : ∃ i : ℕ, i < addOrderOf h ∧ bsH φ h t + i • h = t := by
  obtain ⟨i, hi, he⟩ := exists_pow_orbRep (zH φ h) (tau1P φ t)
  refine ⟨i, by rwa [orderOf_zH] at hi, ?_⟩
  apply tau1P_injective' φ
  rw [tau_add_nsmul, ← orbRep_vOfH]
  exact he

theorem bsH_orb (φ : Formalism.HC.Frame) (h t : φ.A) : ∃ i : ℕ, bsH φ h t + i • h = t := by
  obtain ⟨i, -, hi⟩ := bsH_orb' φ h t
  exact ⟨i, hi⟩

theorem vOfH_bsH (φ : Formalism.HC.Frame) (h t : φ.A) : vOfH φ h (bsH φ h t) = vOfH φ h t := by
  obtain ⟨i, hi⟩ := bsH_orb φ h t
  rw [← vOfH_add_nsmul φ h (bsH φ h t) i, hi]

private theorem bsH_eq_of_vOfH_eq (φ : Formalism.HC.Frame) (h x y : φ.A) (hxy : vOfH φ h x = vOfH φ h y) :
    bsH φ h x = bsH φ h y := by
  unfold bsH
  rw [hxy]

theorem bsH_idem (φ : Formalism.HC.Frame) (h t : φ.A) : bsH φ h (bsH φ h t) = bsH φ h t := by
  exact bsH_eq_of_vOfH_eq φ h _ _ (vOfH_bsH φ h t)

theorem vOfH_injOn (φ : Formalism.HC.Frame) (h : φ.A) : Set.InjOn (vOfH φ h) (Set.range (bsH φ h)) := by
  rintro _ ⟨t1, rfl⟩ _ ⟨t2, rfl⟩ he
  calc bsH φ h t1 = bsH φ h (bsH φ h t1) := (bsH_idem φ h t1).symm
    _ = bsH φ h (bsH φ h t2) := bsH_eq_of_vOfH_eq φ h _ _ he
    _ = bsH φ h t2 := bsH_idem φ h t2

theorem posG_vOfH (φ : Formalism.HC.Frame) (h t : φ.A) (s : Fin (orderOf (zH φ h))) :
    posG (zH φ h) ⟨vOfH φ h t, s⟩ = tau1P φ (bsH φ h t + s.val • h) := by
  rw [posG_apply, orbRep_vOfH, tau_add_nsmul]

end Formalism.L2.G
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.CloudFilling.TauTopPlacesIff
section -- merged from Formalism.LocalToGlobal.GroupLattices.CloudFilling.GatRecStepFrob
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frob_eq (D : D7) {T p : ℕ} (hg : GIdx D.host T p) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) :
    D.host.galE σ = (c0, D.R.iota (hP D p)) := by
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, inferInstance, inferInstance, σ, hσ, rfl⟩
  obtain ⟨P₂, h1, h2, σ₂, hσ₂, he⟩ := Classical.epsilon_spec hne
  have hv := @Formalism.BasicNotions.Examples₂.LevelValuationRings.frob_val _ D.host p hg.1 hg.2.2.1 P₂ h1 h2 σ₂ hσ₂
  have hh : D.R.iota (hP D p) = Formalism.BasicNotions.Examples₂.LevelValuationRings.hOf D.host p := by
    unfold hP
    rw [Formalism.HC.Frame.iota_iotaInv, ← he, hv]
  rw [hh]
  exact Formalism.BasicNotions.Examples₂.LevelValuationRings.frob_val D.host p hg.1 hg.2.2.1 P σ hσ

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

variable (D : D7) (u : D.what₂.Word) {T : ℕ} (hg : GIdx D.host T p)
    (hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zH D.R.toFrame (hP D p))) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ)


include hg in
theorem gatRec_n_frob (v : Fin (gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.nV)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (τ : D.host.E ≃ₐ[ℚ] D.host.E)
    (hτ : IsArithFrobAt ℤ τ P) :
    (gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.n' v =
      orderOf (D.host.galE τ).2 := by
  rw [frob_eq D hg P τ hτ]
  show orderOf (zPsi D.R.toFrame (D.R.iota (hP D p))) = orderOf (D.R.iota (hP D p))
  rw [← Subgroup.orderOf_coe]
  first
  | (rw [show (((zPsi D.R.toFrame (D.R.iota (hP D p))) : D.R.Psi) : D.R.GG) = MonoidHom.inr _ _ (D.R.iota (hP D p)) from rfl]
     exact orderOf_injective _ (fun a b h => congrArg Prod.snd h) _)
  | simp [zPsi, Prod.orderOf]
  | simp [zPsi, Prod.orderOf_mk]


include hg in
theorem gatRec_step_frob (v : Fin (gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.nV)
    (s : Fin ((gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.n' v))
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (τ : D.host.E ≃ₐ[ℚ] D.host.E)
    (hτ : IsArithFrobAt ℤ τ P) :
    ((D.eTau (gatRec_pos D u _ hS r L I ψ y e ⟨v, posAdd s 1⟩) : D.R.Psi) : D.R.GG) =
      ((D.eTau (gatRec_pos D u _ hS r L I ψ y e ⟨v, s⟩) : D.R.Psi) : D.R.GG) *
        D.host.galE τ * D.R.cc := by
  have hz : (((zPsi D.R.toFrame (D.R.iota (hP D p))) : D.R.Psi) : D.R.GG) = D.host.galE τ * D.R.cc := by
    rw [frob_eq D hg P τ hτ]
    refine Prod.ext ?_ ?_
    · show ((1, 1) : G0) = c0 * c0
      first
      | rfl
      | decide
      | simp [c0]
    · show D.R.iota (hP D p) = D.R.iota (hP D p) * 1
      rw [mul_one]
  rw [mul_assoc, ← hz]
  simp only [gatRec_pos, Equiv.trans_apply, Equiv.apply_symm_apply]
  first
  | exact congrArg Subtype.val (posG_step (zPsi D.R.toFrame (D.R.iota (hP D p))) v s)
  | exact congrArg Subtype.val (posG_step v s)
  | exact congrArg Subtype.val (posG_step (z := (zPsi D.R.toFrame (D.R.iota (hP D p)))) v s)

end Formalism.L2.G
end
end

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LatticeCompatibleAt {D : D7} {L : SizeData₂ D} (X : Inst D L) {p : ℕ} (G : GAtP p)
    (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau) (vOf : HH D → Fin G.P.nV) (Fl : Fills G) : Prop :=
  Fl.mm = D.R.m ∧ Fl.t = D.R.t ∧
  (Fl.c : ℝ) ≤ cG L ∧
  G.P.r = (if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1) ∧
  Set.InjOn vOf (reps X p) ∧
  (∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (t : HH D),
    ((D.eTau (pos ⟨v, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau2 t →
      s ∉ Fl.TT v ∧ ∀ j ∈ SizeData₂.lifts D, (Fl.w v j s : ℝ) = fillG X (bL L) j (true, t)) ∧
  ∀ t0 ∈ reps X p,
    G.P.n' (vOf t0) = addOrderOf (hP D p) ∧
    ∀ s : Fin (G.P.n' (vOf t0)),
      ((D.eTau (pos ⟨vOf t0, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau1 (t0 + s.val • hP D p) ∧
      (s ∈ Fl.TT (vOf t0) ↔ t0 + s.val • hP D p ∈ D.host.TT) ∧
      (s ∈ Fl.TT (vOf t0) →
        Fl.a (vOf t0) s = aL L (t0 + s.val • hP D p) ∧
        Fl.b (vOf t0) s = bL L (t0 + s.val • hP D p)) ∧
      ∀ j ∈ SizeData₂.lifts D,
        (Fl.w (vOf t0) j s : ℝ) = fillG X (bL L) j (false, t0 + s.val • hP D p)

theorem latTied_iff {D : D7} {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) :
    LatTied hT X Y ↔ ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      LatticeCompatibleAt X (D.gat u w hg) (hT.gat_pos u w hg) (Y.vOf u w hg) (Y.Fl u w hg) := Iff.rfl

def rRec {D : D7} (L : SizeData₂ D) (p : ℕ) : ℕ := if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1

theorem tau_top_places_iff (D : D7) (t : HH D) : D.R.tau1 t ∈ D.host.topPlaces ↔ t ∈ D.host.TT := by
  rw [← Formalism.MainNotions.Inhab.plGG_false, Formalism.MainNotions.Inhab.plGG_top_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem tau_coe_val (φ : Formalism.HC.Frame) (t : φ.A) : ((tau1P φ t : φ.Psi) : φ.GG) = φ.tau1 t := rfl

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

end Formalism.L2.G
end
end

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure LocPack (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (p : ℕ) where
  W : Type
  Qq : Type
  O : Type
  Kf : Type
  [cW : CommRing W]
  [dW : IsDomain W]
  [vW : IsDiscreteValuationRing W]
  [fQ : Field Qq]
  [aW : Algebra W Qq]
  [cO : CommRing O]
  [dO : IsDomain O]
  [vO : IsDiscreteValuationRing O]
  [fK : Field Kf]
  [aO : Algebra O Kf]
  ι : Qq →+* Kf
  σ : Qq ≃+* Qq
  j : W →+* O
  w : O
  hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w
  I : LocId Lc p (nOrb (zH D.R.toFrame (hP D p))) W Qq
  ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* Oˣ

attribute [instance] LocPack.cW LocPack.dW LocPack.vW LocPack.fQ LocPack.aW LocPack.cO LocPack.dO LocPack.vO LocPack.fK
  LocPack.aO

def rSc (sc : Scale) (k p : ℕ) : ℕ := if (p : ℝ) < sc.p0 k then rG sc else 1

theorem rRec_eq {D : D7} (L : SizeData₂ D) (p : ℕ) : rRec L p = rSc L.sc D.R.k p := rfl

def epSc (R : Ranks) (sc : Scale) (Ce : ℝ) (p : ℕ) : ℕ := ⌈Ce * (R.f : ℝ) * (R.k : ℝ) ^ 2 * Real.logb p sc.a⌉₊

abbrev LocPack.gat {D : D7} {u : D.what₂.Word}
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {p : ℕ} (X : LocPack D u Lc p)
    (r e : ℕ) : GAtP p :=
  gatRec D u (D.R.iota (hP D p)) X.hS r Lc X.I X.ψ (repP Lc p) e

def LocPack.posOK {D : D7} {u : D.what₂.Word}
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {p : ℕ} [Fact p.Prime]
    (X : LocPack D u Lc p) (iK : X.Kf →+* ℂ_[p])
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) : Prop :=
  PosCompat D.host (D.R.iota (hP D p)) X.ι X.σ X.I.iw iK lam

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (X : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocPack D u (Lc u) (D.what₂.places.resChar w))
  (hd : ∀ u w h, ((X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))).d =
    Module.finrank ℂ (D.mem u).A.Mu0)

def recG : D7 :=
  { D with
    gat := fun u w h => (X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))
    gat_d := hd }

def gatTiesG : GatTies (recG D sc Ce Lc X hd) where
  gat_k := fun _ _ _ => k_pred D.R
  gat_n := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) v (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
      (hL : P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})) τ hτ =>
    haveI := hP
    haveI := hL
    gatRec_n_frob D u h (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _) _ v P τ hτ
  gat_pos := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) =>
    gatRec_pos D u _ (X u w h).hS (rSc sc D.R.k (D.what₂.places.resChar w)) (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _)
      (epSc D.R sc Ce (D.what₂.places.resChar w))
  gat_step := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) v s (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
      (hL : P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})) τ hτ =>
    haveI := hP
    haveI := hL
    gatRec_step_frob D u h (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _) _ v s P τ hτ
  gat_lam := fun _ _ _ _ _ _ => rfl

variable (L : SizeData₂ (recG D sc Ce Lc X hd)) (P : ParameterChoice' (recG D sc Ce Lc X hd) L)

def fillsG (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Fills ((recG D sc Ce Lc X hd).gat u w h) :=
  fillsRec D u _ (X u w h).hS (rSc sc D.R.k (D.what₂.places.resChar w)) (Lc u) (X u w h).I (X u w h).ψ
    (repP (Lc u) _) (epSc D.R sc Ce (D.what₂.places.resChar w)) (cRec L) ⟨(cloudBound L P u).top, (cloudBound L P u).off, (cloudBound L P u).fill⟩


def levTieG (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Formalism.L2.Herm.GLevTie (Lc u) ((recG D sc Ce Lc X hd).gat u w h) :=
  gatRecP_lev D u _ (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ _

theorem std_of_fills {p : ℕ} (G : GAtP p) (Fl : Fills G) (v : Fin G.P.nV) (hr : 1 ≤ G.P.r) (h2r : 2 * G.P.r ≤ G.P.m + 1)
    (hm : 1 ≤ Fl.mm) :
    Formalism.MainNotions.FormalGroupSystem.Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v) :=
  { prime := (G.P.setting v).prime
    five_le := (G.P.setting v).five_le
    two_le := (G.P.setting v).two_le
    even := (G.P.setting v).even
    r_pos := hr
    two_r := h2r
    m_pos := hm
    base := Fl.base v
    dom := G.P.dom v
    w_low := fun s => ⟨le_trans (le_max_left _ _) (Fl.w_ge v s), le_trans (le_max_right _ _) (Fl.w_ge v s)⟩
    w_mono := fun s l h1 _ => Fl.w_mono v s l h1 }

theorem one_le_rSc (k p : ℕ) : 1 ≤ rSc sc k p := by
  unfold rSc rG
  split_ifs <;> omega

theorem two_rSc_le (k p : ℕ) (h : 2 * rG sc ≤ k) : 2 * rSc sc k p ≤ k := by
  unfold rSc
  split_ifs
  · exact h
  · unfold rG at h
    omega

theorem stdG (h2r : 2 * rG sc ≤ D.R.k) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin ((recG D sc Ce Lc X hd).gat u w h).P.nV) :
    Formalism.MainNotions.FormalGroupSystem.Std (D.what₂.places.resChar w) (((recG D sc Ce Lc X hd).gat u w h).P.n' v) ((recG D sc Ce Lc X hd).gat u w h).P.m
      (fillsG D sc Ce Lc X hd L P u w h).t (fillsG D sc Ce Lc X hd L P u w h).mm (fillsG D sc Ce Lc X hd L P u w h).c
      ((recG D sc Ce Lc X hd).gat u w h).P.r ((fillsG D sc Ce Lc X hd L P u w h).TT v) ((fillsG D sc Ce Lc X hd L P u w h).a v)
      ((fillsG D sc Ce Lc X hd L P u w h).b v) (((recG D sc Ce Lc X hd).gat u w h).P.lam0 v)
      ((fillsG D sc Ce Lc X hd L P u w h).w v) := by
  refine std_of_fills _ _ v ?_ ?_ ?_
  · exact one_le_rSc sc _ _
  · have h1 := two_rSc_le sc D.R.k (D.what₂.places.resChar w) h2r
    have h2 := D.R.m_add_three_le_k
    show 2 * rSc sc D.R.k (D.what₂.places.resChar w) ≤ D.R.k - 1 + 1
    omega
  · have := D.R.two_le_m
    show 1 ≤ D.R.m
    omega

end Formalism.L2.G
