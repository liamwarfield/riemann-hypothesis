module

public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainK
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.GramDetIsUnit
public import Formalism.LocalToGlobal.HermitianColumns.ZeroPointScaledByCharacter
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.PNeZeroOL
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem
open scoped TensorProduct

namespace Formalism.L2.G.Pend

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem std_of {p : ℕ} (G : GAtP p) (Fl : Fills G) (hr1 : 1 ≤ G.P.r) (hr2 : 2 * G.P.r ≤ G.P.m + 1) (hm : 1 ≤ Fl.mm)
    (v : Fin G.P.nV) :
    Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v) :=
  { prime := (G.P.setting v).prime
    five_le := (G.P.setting v).five_le
    two_le := (G.P.setting v).two_le
    even := (G.P.setting v).even
    r_pos := hr1
    two_r := hr2
    m_pos := hm
    base := Fl.base v
    dom := G.P.dom v
    w_low := fun s => ⟨le_trans (le_max_left _ _) (Fl.w_ge v s), le_trans (le_max_right _ _) (Fl.w_ge v s)⟩
    w_mono := fun s l hl _ => Fl.w_mono v s l hl }

section Chain

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) {LL : Type} [Field LL] (e : LL →+* G.Kf) (m : ℕ)
  (V : ℕ → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module LL (V j)] (ix : ℕ → Type) (b : ∀ j, Module.Basis (ix j) LL (V j))
  (cmp : ∀ j, V j →ₛₗ[e] Lv.Fm j) (li : ∀ j, j ≤ m → LinearIndependent G.Kf fun a => cmp j (b j a))
  (KL : ∀ j, V j →ₗ[LL] V (j + 1))


end Chain

section Ring

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (L : IntermediateField (KO p n) (Om p n)) [FiniteDimensional (KO p n) L]

instance charZeroL : CharZero L := charZero_of_injective_algebraMap (algebraMap (KO p n) L).injective

theorem p_ne_zero_OL : (p : OL p n L) ≠ 0 := by
  intro h0
  have h1 := congrArg (algebraMap (OL p n L) L) h0
  rw [map_natCast, map_zero] at h1
  exact (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : L) ≠ 0) h1

end Ring

section Record

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)

abbrev gatL : GAtP p := gatRecP D u h (settingOL p (orderOf (zPsi D.R.toFrame h)) L h5 h2 he) r Lc I ψ e

def cembL : CEmb (gatL D u h L h5 h2 he r Lc I ψ e) := ⟨embLC (k0ToC p) L, embLC_int' L⟩

theorem compat_L : Compat (gatL D u h L h5 h2 he r Lc I ψ e) (cembL D u h L h5 h2 he r Lc I ψ e)
    (fun _ => rdW p (orderOf (zPsi D.R.toFrame h))) :=
  fun _ s x => compat_conc L s x

end Record

section Record2

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)

abbrev fillsL : Fills (gatL D u h L h5 h2 he r Lc I ψ e) :=
  fillsRec D u h (settingOL p (orderOf (zPsi D.R.toFrame h)) L h5 h2 he) r Lc I ψ (repP Lc p) e c hc

theorem std_L (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (v : Fin (gatL D u h L h5 h2 he r Lc I ψ e).P.nV) :
    Std p ((gatL D u h L h5 h2 he r Lc I ψ e).P.n' v) (gatL D u h L h5 h2 he r Lc I ψ e).P.m
      (fillsL D u h L h5 h2 he r Lc I ψ e c hc).t (fillsL D u h L h5 h2 he r Lc I ψ e c hc).mm
      (fillsL D u h L h5 h2 he r Lc I ψ e c hc).c (gatL D u h L h5 h2 he r Lc I ψ e).P.r
      ((fillsL D u h L h5 h2 he r Lc I ψ e c hc).TT v) ((fillsL D u h L h5 h2 he r Lc I ψ e c hc).a v)
      ((fillsL D u h L h5 h2 he r Lc I ψ e c hc).b v) ((gatL D u h L h5 h2 he r Lc I ψ e).P.lam0 v)
      ((fillsL D u h L h5 h2 he r Lc I ψ e c hc).w v) :=
  std_of _ _ hr1 (by
    show 2 * r ≤ D.R.k - 1 + 1
    rw [k_pred]
    exact hr2) (by
    show 1 ≤ D.R.m
    exact le_trans (by norm_num) D.R.two_le_m) v

variable (Lv : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc)) (Ch : Chain Lv)
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (hfin : ∀ j c', (Lv.lev j c').FinClasses)

abbrev sysL : Sys p :=
  sysC (gatL D u h L h5 h2 he r Lc I ψ e) (fillsL D u h L h5 h2 he r Lc I ψ e c hc) Lv Ch
    (std_L D u h L h5 h2 he r Lc I ψ e c hc hr1 hr2) hfin (p_ne_zero_OL L)

end Record2

section Record3

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (Lv : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc)) (Ch : Chain Lv)
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (hfin : ∀ j c', (Lv.lev j c').FinClasses) (hst : FinStab Lv)

abbrev posL : (Σ v : (sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).Pl,
    Fin ((sysL D u h L h5 h2 he r Lc I ψ e c hc Lv Ch hr1 hr2 hfin).G.P.n' v)) ≃ D.what₂.Tau :=
  gatRec_pos D u h (settingOL p (orderOf (zPsi D.R.toFrame h)) L h5 h2 he) r Lc I ψ (repP Lc p) e

end Record3

section ChainF

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) {D : D7} (Tw : TwForms D) (u : D.what₂.Word)
  (w : D.what₂.places.Pl) (eL : D.what₂.LL →+* G.Kf)
  (cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[eL] Lv.Fm j)
  (li : ∀ j, j ≤ D.R.m → LinearIndependent G.Kf fun a => cmp j (((Tw.fm u (D.what₂.muAt w)).lat j).b a))

end ChainF

end Formalism.L2.G.Pend
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CembCL
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem
open scoped TensorProduct

namespace Formalism.L2.G.Pend

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)

def cembCL : CEmbC (gatL D u h L h5 h2 he r Lc I ψ e) where
  toCEmb := cembL D u h L h5 h2 he r Lc I ψ e
  rd := fun _ => rdW p (orderOf (zPsi D.R.toFrame h))
  compat := compat_L D u h L h5 h2 he r Lc I ψ e

variable (c : ℕ) (hc : CloudBound D u c)
  (Lv : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc)) (Ch : Chain Lv)
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (hfin : ∀ j c', (Lv.lev j c').FinClasses) (hst : FinStab Lv)
  {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g)

end Formalism.L2.G.Pend
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.PendingLemmas.RecLev
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem
open scoped TensorProduct

namespace Formalism.L2.G.Pend

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record4

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)

variable (hg : ∀ a, D.host.g a ≠ 0) (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))

abbrev levelsL : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc) :=
  levelsRec D u h (settingOL p (orderOf (zPsi D.R.toFrame h)) L h5 h2 he) r Lc I ψ (repP Lc p) e c hc hg hpg Cb Sx

variable (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)
  (hst : FinStab (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g)

abbrev sysRec : Sys p :=
  sysL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin

end Record4

end Formalism.L2.G.Pend
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtRec
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (hg : ∀ a, D.host.g a ≠ 0)
  (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))
  (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)

variable (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))


include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in
def ptRec : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j →
    PtD D.host.F D.host.E (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
  | 0, La => ptStep0 (I := I) (isUnit_det_gram0 D.sp) (k_pred D.R) (repP Lc p) a bad La.1 La.2
  | i + 1, La =>
      let X := Sx i La.1.1 La.1.2.1
      let S : StepG I (D.sp.X (i + 1)).rank :=
        { J := (D.sp.X (i + 1)).gram
          hJ := gram_herm D.sp.cm (D.sp.X (i + 1))
          hdet := gram_det_unit D.sp.cm (D.sp.X (i + 1))
          Lb := X.lev.Lb
          Uloc := X.lev.Uloc
          fr := X.fr
          U := X.lev.U
          U_eq := X.lev.U_eq }
      ptStep S (rank_step D i La.1.1) a bad La.1.2.2 La.2

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1) → Formalism.L2.Col.HomE D.host.E
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)



include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in
def twC (v : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pl) (s : Fin ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).G.P.n' v)) : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).G.P.Qq v →+* ℂ_[p] :=
  letI := algKfC (cembCL D u h L h5 h2 he r Lc I ψ e).toCEmb
  tw (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin) ℂ_[p] v s


variable {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g)


variable (hst : FinStab (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))

end Formalism.L2.PairingIndexBounds.F
end
end

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.G.Cmp
open Formalism.L2.Col Formalism.HermitianLatticesTheory
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (hg : ∀ a, D.host.g a ≠ 0)
  (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))
  (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)

variable (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1) → Formalism.L2.Col.HomE D.host.E
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)


include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in
def OrthTie : Prop :=
  (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 co) ∧
    ∀ i, i < D.R.m → ∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram co


include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in
def ATie : Prop :=
  compan (sp := D.sp) D.sp.gram0 a Lc.Lb = D.sp.crdLat0 (D.sp.X 0).L0 ∧
    ∀ (i : ℕ) (hi : i < D.R.m) (β : Cb i hi), compan (sp := D.sp) (D.sp.X (i + 1)).gram a (Sx i hi β).lev.Lb =
      Formalism.L2.Herm.crdLat (D.sp.X (i + 1)) (D.sp.X (i + 1)).L0

def MuTie (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  ∀ j, muT j 1 = 1 ∧ (∀ x y, muT j (x * y) = muT j x * muT j y) ∧ ∀ x, muT j x ≠ 0 ∧ muT j x ∈ TaylorLogMetric.Qbar


include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in
def baseComp : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → Submodule (𝓞 D.host.E) (Fin (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) → D.host.E)
  | 0, _ => (compan (sp := D.sp) D.sp.gram0 a Lc.Lb).map
      ((reE (E := D.host.E) (k_pred D.R).symm).toLinearMap.restrictScalars (𝓞 D.host.E))
  | i + 1, La => (compan (sp := D.sp) (D.sp.X (i + 1)).gram a (Sx i La.1.1 La.1.2.1).lev.Lb).map
      ((reE (E := D.host.E) (rank_step D i La.1.1).symm).toLinearMap.restrictScalars (𝓞 D.host.E))






include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in
def LamPos : Prop :=
  ∀ (τ : D.what₂.Tau) (x : D.host.E) (hx : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar),
    lam ⟨TaylorLogMetric.embT D τ x, hx⟩ =
      twC D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1 ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).2
        ((I.eQ ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1).symm
          (fstV I ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1 (inclE (F := D.host.F) (((I.plc ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1)).adicCompletion D.host.F)
            (if IsOddPos ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).2 then D.host.conj x else x))))

end Formalism.L2.PairingIndexBounds.F
