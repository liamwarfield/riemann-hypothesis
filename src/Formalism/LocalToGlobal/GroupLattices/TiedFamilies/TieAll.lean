module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieEvR
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieExC
section -- merged from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtC
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section C

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)


set_option maxHeartbeats 4000000 in
theorem hypT_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    HypT ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) :=
  hypT_of (hL u) _ (I u w hg) (levTieOf_fr (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg))
    (levTieOf_spl (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg)) (isHyperbolicAt_rec_of_placeIdentification D u w hg (I u w hg))

end C

end Formalism.L2.G
end
end

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)


set_option maxHeartbeats 8000000 in
theorem ptOne_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    PtOne ((T u).cls0).lev ((recC D sc Ce Lc I ψ hd).gat u w hg)
      (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B) :=
  ptOne_rec (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u hU w hg B (frRat_C D sc Ce Lc I ψ hd H0 hL B hB u w hg)
    (hypT_C D sc Ce Lc I ψ hd H0 hL u w hg)


set_option maxHeartbeats 8000000 in
theorem ex_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (h1 : EvRatRep (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL ((recC D sc Ce Lc I ψ hd).gat u w hg)
      (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u))
    (h2 : LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u) :
    ValEx ((T u).cls0).lev (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL
      ((recC D sc Ce Lc I ψ hd).gat u w hg) (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B)
      ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u) ((T u).cls0).y :=
  ex_rec (D := recC D sc Ce Lc I ψ hd) (X := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T (gatTiesC D sc Ce Lc I ψ hd)
    (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) u w hg
    (ptOne_C D sc Ce Lc I ψ hd H0 hL T B hB u hU w hg) h1 h2


set_option maxHeartbeats 8000000 in
theorem ex_C_blk (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (h1 : BlockRationalityAtPlace (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) (gatTiesC D sc Ce Lc I ψ hd) u w hg B)
    (h2 : LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u) :
    ValEx ((T u).cls0).lev (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL
      ((recC D sc Ce Lc I ψ hd).gat u w hg) (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B)
      ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u) ((T u).cls0).y :=
  ex_C D sc Ce Lc I ψ hd H0 hL T B hBs hB u hU w hg
    (evRatRep_rec (D := recC D sc Ce Lc I ψ hd) (X := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T
      (gatTiesC D sc Ce Lc I ψ hd) u w hg B h1) h2

end Formalism.L2.G
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms Formalism.L2.G.Cmp

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
  (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
  (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
  (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)

structure CmpLeft : Prop where
  same : ∀ u, SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u
  blk : ∀ u w hg, BlockRationalityAtPlace (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) (gatTiesC D sc Ce Lc I ψ hd) u w hg B
  psi0 : ∀ u, LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u
  chi : ∀ u w hg i (γ : (((recC D sc Ce Lc I ψ hd).gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap ((recC D sc Ce Lc I ψ hd).gat u w hg).O ((recC D sc Ce Lc I ψ hd).gat u w hg).Kf
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).lev i).χ γ : ((recC D sc Ce Lc I ψ hd).gat u w hg).O) *
          (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg r = 1
  valInt : ValIntRec T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB)

variable {D sc Ce Lc I ψ hd H0 hL T B hBs hB}


set_option maxHeartbeats 8000000 in
theorem CmpLeft.core (N : CmpLeft D sc Ce Lc I ψ hd H0 hL T B hBs hB)
    (pos : ∀ u w hg v (s : Fin (((recC D sc Ce Lc I ψ hd).gat u w hg).P.n' v)) (x : D.host.E),
      (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
        (tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
          (if Even s.val then x else sigD (recC D sc Ce Lc I ψ hd) x)) =
        ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x))) :
    CmpCore T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) :=
  { same := N.same
    ex := fun u w hg => ex_C D sc Ce Lc I ψ hd H0 hL T B hBs hB u (N.same u) w hg
      (evRatRep_rec T (gatTiesC D sc Ce Lc I ψ hd) u w hg B (N.blk u w hg)) (N.psi0 u)
    pos := pos
    chi := N.chi }


set_option maxHeartbeats 8000000 in
theorem CmpLeft.toHyp0P (N : CmpLeft D sc Ce Lc I ψ hd H0 hL T B hBs hB)
    (pos : ∀ u w hg v (s : Fin (((recC D sc Ce Lc I ψ hd).gat u w hg).P.n' v)) (x : D.host.E),
      (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
        (tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
          (if Even s.val then x else sigD (recC D sc Ce Lc I ψ hd) x)) =
        ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x))) :
    CmpHyp0P T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) :=
  cmpHyp0P_of_cmpCore (N.core pos)
    (fun u w hg => gatIs_recC D sc Ce Lc I ψ hd H0 hL (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg) N.valInt

end Formalism.L2.G
