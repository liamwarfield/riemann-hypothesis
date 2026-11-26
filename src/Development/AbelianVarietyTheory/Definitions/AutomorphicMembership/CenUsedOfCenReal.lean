module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure PrN : Prop where
  what₂ : GlobalTheory.NRows.Hypotheses₂
  decay : GlobalTheory.Published.CuspRapidDecay
  hc : GlobalTheory.Published.HarishChandraFinite
  greenC : GlobalTheory.Published.GreenCuspidal
  green : GlobalTheory.GLq.Green
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  dz : GlobalTheory.Published.DepthZeroInertia
  ray : GlobalTheory.Published.RayClassFieldSt
  rayF : GlobalTheory.NT.RayField
  rayA : GlobalTheory.Published.RayCharacterArtin
  bc : GlobalTheory.Published.BaseChangeDefiniteUnitary
  ds : GlobalTheory.Published.DiscreteSpectrumGL
  gen : GlobalTheory.Published.GenericUnitaryDualGL
  std : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  howe : GlobalTheory.Hk3.HoweUnram

structure SerN : Prop where
  rat : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat
  int : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt
  hkInt : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt
  hkTr : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform
  hkRead : GlobalTheory.HeckeSupSt.HeckeReadTie
  ratio : GlobalTheory.ToricRational.RatioConj

def RootsLL (D : D7) : Prop := ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ D.what₂.restRowsFiniteGroupCard

end GlobalTheory.HeightCounting.Up

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PadTrueNormDetConst
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.Pad

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag)
  {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (Φ.C k) C)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))
  (hj : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) (hA : AdmEx S κ) {ng : NgPkg}

def padTrue (L : LocSt D N j ng) (G : GlobSt fun p => (L.loc p).Mdl) : PadPkg D N j s.Comp jC ng :=
  padAt s L G (admissible_representation_factorisation S κ jC hj hA) (flatSt s Φ hm) (arIn s Φ hm)

variable (L : LocSt D N j ng) (G : GlobSt fun p => (L.loc p).Mdl)

section Prime

open PadPkg (md)

variable {p : ℕ} [Fact p.Prime] {la : PlL D p}

end Prime

end GlobalTheory.ShFam.Pad
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

variable {D : D7}

abbrev StFams (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A), StFam S κ

section One

variable {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (F : StFam S κ) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D)

abbrev PolOf {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) : Type := PolDat s Φ (metsOf x Φ) (refMet x Φ)

abbrev padWith {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) (cts : Ats S κ) {jC : JC D} (hj : jC.Pinned) (hA : AdmEx S κ) :
    PadPkg D N j s.Comp jC ngTrue :=
  padTrue s Φ (metsOf x Φ) jC hj hA (locStOf F cts) (globStOf F cts)

structure IsKitWith (k : KitT s L jC) (d : s.Comp → D.what₂.Tau → ℝ) (x : ToroidalCompactificationData s) (P : PolOf x k.Φ) (cts : Ats S κ)
    (hj : jC.Pinned) (hA : AdmEx S κ) : Prop where
  ats : cts.Over jC
  bd : IsBdOf x L k.B
  fl : k.fl = flBetti s k.Φ L
  mb : k.Mb = mbarOf P
  pad : k.pad = padWith F x k.Φ cts hj hA
  deg : d = degFlat s k.Φ (metsOf x k.Φ)

namespace IsKitWith

variable {F s L jC} {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ} {cts : Ats S κ}
  {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA)
include h


end IsKitWith

end One

def IsKitOf (st : StFams D) : KitClass D := fun A N j S κ s L jC k d =>
  ∃ x P cts hj hA, IsKitWith (st A N j S κ) s L jC k d x P cts hj hA

namespace IsKitOf

variable {st : StFams D} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {L : CmList A} {jC : JC D}
  {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} (h : IsKitOf st A N j S κ s L jC k d)
include h

end IsKitOf

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists
noncomputable section

namespace GlobalTheory.HeightCounting.Up.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem qOf_off (v : B.places.Pl) (h : v ∉ P.Wt) : QOf P v = ∅ := if_neg h

theorem qOf_on (v : B.places.Pl) (h : v ∈ P.Wt) : QOf P v = T.Q v := if_pos h

theorem qOf_eq (v : B.places.Pl) : QOf P v = T.Q v := by
  by_cases h : v ∈ P.Wt
  · exact qOf_on v h
  · rw [qOf_off v h]
    refine (Finset.eq_empty_of_forall_notMem fun u hu => ?_).symm
    have h1 := ((T.psi_is v).ram u).1 (by rw [P.supp v h]; exact fun _ _ => rfl)
    exact h1 hu

theorem mem_of_twisted (x : St P) (v : B.places.Pl) (h : TwistedAt (Dof x) v) : v ∈ P.Wt := by
  by_contra hv
  exact h (P.q.mu.off v hv)

theorem del_mul_ne_one {p : ℕ} (hp : p.Prime) (hS : p ∈ offSet B.toPre) {δ : HChar B.host.E} (hδ : IsDelta (H := B.host) p δ)
    (v : B.places.Pl) : δ * T.psi v ≠ 1 := by
  intro h
  obtain ⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal (𝓞 B.host.E), Q.IsMaximal ∧ ((p : ℕ) : 𝓞 B.host.E) ∈ Q := by
    have hne : Ideal.span {((p : ℕ) : 𝓞 B.host.E)} ≠ ⊤ := by
      intro ht
      have := congrArg Ideal.absNorm ht
      rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at this
      have h2 : Algebra.norm ℤ ((p : ℕ) : 𝓞 B.host.E) = (p : ℤ) ^ Module.finrank ℤ (𝓞 B.host.E) := by
        rw [← map_natCast (algebraMap ℤ (𝓞 B.host.E)), Algebra.norm_algebraMap]
      rw [h2, Int.natAbs_pow, Int.natAbs_natCast] at this
      rcases Nat.pow_eq_one.1 this with h3 | h3
      · exact hp.one_lt.ne' h3
      · exact Module.finrank_pos.ne' h3
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ⟨Q, hQ, hle (Ideal.subset_span rfl)⟩
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hpQ))
  let u : HeightOneSpectrum (𝓞 B.host.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hu : OverP B.host p u := hpQ
  have hψ : (T.psi v).UnrAt u := by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 u hn
    have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 B.host.E) ∈ u.asIdeal := Ideal.absNorm_mem _
    by_cases e : Ideal.absNorm u.asIdeal = p
    · exact h2 (e ▸ hS)
    · obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 B.host.E) (p : 𝓞 B.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes h1 hp).2 e)
      exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ hpQ)))
  have h15 := (hδ.ine u hu 1).1 fun x hx => by
    have e := congrArg (fun χ : HChar B.host.E => χ.loc u x) h
    change δ.loc u x * (T.psi v).loc u x = 1 at e
    rw [hψ x hx, mul_one] at e
    rw [pow_one, e]
  omega

theorem twisted_iff (x : St P) (v : B.places.Pl) : TwistedAt (Dof x) v ↔ v ∈ P.Wt := by
  refine ⟨mem_of_twisted x v, fun hv h => ?_⟩
  have h1 : P.q.W₀.muTw v = w.C.mu0 := (P.q.mu.on v hv).symm.trans h
  have h2 := P.q.mu.tw v
  rw [h1] at h2
  have h3 : T.xiTw f v = 1 := h2.symm.trans w.ok.trueColumnChoices_heckeChar_reference_eq_one
  unfold TwDat.xiTw at h3
  split_ifs at h3
  · exact del_mul_ne_one B.host.pde'_prime (by simp [offSet]) f.isDel' v h3
  · exact del_mul_ne_one B.host.pde_prime (by simp [offSet]) f.isDel v h3

end GlobalTheory.HeightCounting.Up.Model

end
end
