module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveProjBundleModelCochainComplexX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainMapOfFibreCocyclePairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainMapOfFibreCocyclePairing
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC.PsiModel
variable {R : Type} [CommRing R]

theorem map_sres {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sx.map f (Sx.res g x) = Sx.res g (Sx.map f x) := by
  unfold Sx.map Sx.res
  exact NatTrans.naturality_apply (f.app (op (SimplexCategory.mk p))) g.op x

theorem map_face {E E' : Spc} (f : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (x : Sx E (p + 1) U) (i : Fin (p + 2)) :
    Sx.map f (Sx.face x i) = Sx.face (Sx.map f x) i := by
  unfold Sx.map Sx.face
  have h1 := NatTrans.congr_app (f.naturality (SimplexCategory.δ i).op) (op U)
  simp only [NatTrans.comp_app] at h1
  have h2 := ConcreteCategory.congr_hom h1 x
  simp only [ConcreteCategory.comp_apply] at h2
  exact h2

theorem map_map {E E' E'' : Spc} (f : E ⟶ E') (f' : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    Sx.map f' (Sx.map f x) = Sx.map (f ≫ f') x := rfl

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  simp [Sec.res]

theorem ev_smul {E : Spc} {I : Cx R} {n : ℤ} (r : ULift.{1} R) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (R := R) (r • α) p s h U x = r • ev (R := R) α p s h U x := by
  rw [ev_def, ev_def, Cochain.smul_v, Linear.comp_smul]
  rfl

variable {q N : ℕ}

def fstH {U V : Scheme.{0}} {p : ℕ} (y : Sx (sch.obj U ⨯ fibQ q N) p V) : V ⟶ U :=
  Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y

theorem fstH_res {U V' V : Scheme.{0}} {p : ℕ} (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V) :
    fstH (Sx.res g y) = g ≫ fstH y := by
  unfold fstH
  rw [map_sres]
  rfl

theorem fstH_face {U V : Scheme.{0}} {p : ℕ} (y : Sx (sch.obj U ⨯ fibQ q N) (p + 1) V) (i : Fin (p + 2)) :
    fstH (Sx.face y i) = fstH y := by
  unfold fstH
  rw [map_face]
  rfl

theorem fstH_map {U U' V : Scheme.{0}} {p : ℕ} (g : U' ⟶ U) (y : Sx (sch.obj U' ⨯ fibQ q N) p V) :
    fstH (Sx.map (prod.map (sch.map g) (𝟙 (fibQ q N))) y) = fstH y ≫ g := by
  unfold fstH
  rw [map_map, prod.map_fst]
  rfl

theorem snd_map {U U' V : Scheme.{0}} {p : ℕ} (g : U' ⟶ U) (y : Sx (sch.obj U' ⨯ fibQ q N) p V) :
    Sx.map (prod.snd : sch.obj U ⨯ fibQ q N ⟶ _) (Sx.map (prod.map (sch.map g) (𝟙 (fibQ q N))) y) = Sx.map prod.snd y := by
  rw [map_map, prod.map_snd, Category.comp_id]

variable {I₁ I₂ K : Cx R} (μ : Pair I₁ I₂ K) {n : ℤ} (z : Cochain ((chains R).obj (fibQ q N)) I₂ n)

def pval {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V) : Sec (K.X s) V :=
  μ.mul V m (-(p : ℤ) + n) s (by omega) (Sec.res (fstH y) a) (ev (R := R) z p (-(p : ℤ) + n) rfl V (Sx.map prod.snd y))

theorem pval_res {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    {V' V : Scheme.{0}} (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V) :
    Sec.res g (pval μ z hw a p s hs V y) = pval μ z hw a p s hs V' (y.res g) := by
  unfold pval
  rw [μ.nat, res_res, ev_res, map_sres, fstH_res]

def cval {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) :
    Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) K w :=
  (CupSpec.ev_exists (pval μ z hw a) (fun p s hs V' V g y => pval_res μ z hw a p s hs g y)).choose

theorem cval_ev {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V) : ev (R := R) (cval μ z hw a) p s hs V y = pval μ z hw a p s hs V y :=
  (CupSpec.ev_exists (pval μ z hw a) (fun p s hs V' V g y => pval_res μ z hw a p s hs g y)).choose_spec p s hs V y

theorem cval_add {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a b : Sec (I₁.X m) U) :
    cval μ z hw (a + b) = cval μ z hw a + cval μ z hw b := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_add, cval_ev, cval_ev, cval_ev]
  unfold pval
  rw [show Sec.res (fstH y) (a + b) = Sec.res (fstH y) a + Sec.res (fstH y) b from map_add _ _ _, LinearMap.map_add₂]

theorem cval_smul {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (r : ULift.{1} R) (a : Sec (I₁.X m) U) :
    cval μ z hw (r • a) = r • cval μ z hw a := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_smul, cval_ev, cval_ev]
  unfold pval
  rw [show Sec.res (fstH y) (r • a) = r • Sec.res (fstH y) a from map_smul _ _ _, LinearMap.map_smul₂]

theorem cval_nat {U U' : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (g : U' ⟶ U) (a : Sec (I₁.X m) U) :
    cval μ z hw (Sec.res g a) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (cval μ z hw a) (zero_add w) := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_pull, cval_ev, cval_ev]
  unfold pval
  rw [fstH_map, snd_map, res_res]

def pmor {m w : ℤ} (hw : m + n = w) : (I₁.X m).obj ⟶ cotPre R q N K w where
  app U := ModuleCat.ofHom
    { toFun := fun a => cval μ z hw (U := U.unop) a
      map_add' := cval_add μ z hw
      map_smul' := cval_smul μ z hw }
  naturality U U' f := by
    ext a : 2
    exact cval_nat μ z hw f.unop a

def smor {m w : ℤ} (hw : m + n = w) : I₁.X m ⟶ (Jcx R q N K).X w :=
  ObjectProperty.homMk (pmor μ z hw ≫ toSheafify Scheme.etaleTopology.{0} (cotPre R q N K w))

def psiC : Cochain I₁ (Jcx R q N K) n := Cochain.mk fun m w hw => smor μ z hw

theorem psiC_v {m w : ℤ} (hw : m + n = w) : (psiC μ z).v m w hw = smor μ z hw := Cochain.mk_v _ _ _ _

theorem Jcx_d (w : ℤ) : (Jcx R q N K).d w (w + 1) = (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N K w) := by
  simp [Jcx]

theorem mul_d_congr {V : Scheme.{0}} {m T t1 t2 w : ℤ} (e : t1 = t2) (h1 : m + t1 = w) (h2 : m + t2 = w)
    (A : Sec (I₁.X m) V) (B : Sec (I₂.X T) V) :
    μ.mul V m t1 w h1 A (Sec.map (I₂.d T t1) B) = μ.mul V m t2 w h2 A (Sec.map (I₂.d T t2) B) := by
  subst e
  rfl

theorem cval_δ (hn : Even n) (hz : δ n (n + 1) z = 0) {U : Scheme.{0}} {m w w' : ℤ} (hw : m + n = w)
    (hw' : m + 1 + n = w') (a : Sec (I₁.X m) U) :
    δ w w' (cval μ z hw a) = cval μ z hw' (Sec.map (I₁.d m (m + 1)) a) := by
  have hww : w + 1 = w' := by omega
  refine ev_ext _ _ fun k t ht V y => ?_
  rcases k with _ | k
  · rw [ev_δ_zero hww _ V w t (by simp) ht y, cval_ev, cval_ev]
    unfold pval
    obtain rfl : t = w + 1 := by simp at ht; omega
    rw [μ.leibniz]
    have hz0 : Sec.map (I₂.d (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + n + 1))
        (ev (R := R) z 0 (-((0 : ℕ) : ℤ) + n) rfl V (Sx.map prod.snd y)) = 0 := by
      rw [← ev_δ_zero (n := n) (m := n + 1) rfl z V _ _ rfl (by omega), hz, ev_zero]
    rw [hz0, map_zero, smul_zero, add_zero, map_res]
  · rw [ev_δ_succ hww _ V k (-((k + 1 : ℕ) : ℤ) + w) t rfl ht y, cval_ev]
    obtain rfl : t = -((k + 1 : ℕ) : ℤ) + w + 1 := by omega
    have e2 : ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := R) (cval μ z hw a) k (-((k + 1 : ℕ) : ℤ) + w + 1) (by omega) V (y.face i) =
        ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • μ.mul V m (-(k : ℤ) + n) (-((k + 1 : ℕ) : ℤ) + w + 1) (by omega)
          (Sec.res (fstH y) a) (ev (R := R) z k (-(k : ℤ) + n) rfl V ((Sx.map prod.snd y).face i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cval_ev]
      unfold pval
      rw [fstH_face, map_face]
    rw [e2, cval_ev]
    unfold pval
    rw [μ.leibniz, mul_d_congr μ (t2 := -(k : ℤ) + n) (by push_cast; omega) _ (by push_cast; omega)]
    have hzS := ev_δ_succ (n := n) (m := n + 1) rfl z V k (-((k + 1 : ℕ) : ℤ) + n) (-(k : ℤ) + n) rfl (by push_cast; omega)
      (Sx.map prod.snd y)
    rw [hz, ev_zero, Int.negOnePow_succ, Int.negOnePow_even n hn, Units.neg_smul, one_smul, eq_comm,
      add_neg_eq_zero] at hzS
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hzS, map_sum, ← map_res]
    have hs : w'.negOnePow = -m.negOnePow := by
      rw [← hw', Int.negOnePow_add, Int.negOnePow_succ, Int.negOnePow_even n hn, mul_one]
    simp only [map_zsmul]
    rw [hs, Units.neg_smul]
    exact add_neg_cancel_right _ _

theorem psiC_δ (hn : Even n) (hz : δ n (n + 1) z = 0) : δ n (n + 1) (psiC μ z) = 0 := by
  refine Cochain.ext _ _ fun p q' hpq => ?_
  obtain ⟨w, rfl⟩ : ∃ w, q' = w + 1 := ⟨q' - 1, by omega⟩
  rw [δ_v n (n + 1) rfl _ p (w + 1) hpq w (p + 1) (by omega) rfl, psiC_v, psiC_v, Jcx_d, Int.negOnePow_succ,
    Int.negOnePow_even n hn, Cochain.zero_v, Units.neg_smul, one_smul, add_neg_eq_zero]
  apply Sheaf.hom_ext
  change pmor μ z _ ≫ toSheafify _ _ ≫ sheafifyMap _ (cotD R q N K w) =
    (I₁.d p (p + 1)).hom ≫ pmor μ z _ ≫ toSheafify _ _
  rw [← toSheafify_naturality, ← Category.assoc, ← Category.assoc]
  congr 1
  ext U : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact cval_δ μ z hn hz _ _ a

end GlobalTheory.EtC.PsiModel

namespace GlobalTheory.EtC.PsiModel

theorem psi_exists : ∀ (q N : ℕ) (i₁ i₂ i : ℤ) (h : i₁ + i₂ = i) (d : ℕ) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) (2 * (d : ℤ))), ∃ ψ : Cocycle (res (ZMod q) (tw q i₁)) (Jcx (ZMod q) q N (res (ZMod q) (tw q i))) (2 * (d : ℤ)), ∀ (m w : ℤ) (hw : m + 2 * (d : ℤ) = w) (U : Scheme.{0}) (a : Sec ((res (ZMod q) (tw q i₁)).X m) U), ∃ c : Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) (res (ZMod q) (tw q i)) w, Sec.map (ψ.1.v m w hw) a = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + w = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev (R := ZMod q) c k s hs V y = twCast h ((twPair q i₁ i₂).mul V m (-(k : ℤ) + 2 * (d : ℤ)) s (by omega) (Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U) a) (ev (R := ZMod q) z.1 k (-(k : ℤ) + 2 * (d : ℤ)) rfl V (Sx.map prod.snd y))) := by
  intro q N i₁ i₂ i h d z
  subst h
  refine ⟨Cocycle.mk (psiC (twPair q i₁ i₂) z.1) (2 * (d : ℤ) + 1) rfl
    (psiC_δ _ _ (even_two_mul _) (z.δ_eq_zero _)), fun m w hw U a => ⟨cval (twPair q i₁ i₂) z.1 hw a, ?_, fun k s hs V y => ?_⟩⟩
  · change Sec.map ((psiC (twPair q i₁ i₂) z.1).v m w hw) a = _
    rw [psiC_v]
    rfl
  · rw [cval_ev]
    rfl

end GlobalTheory.EtC.PsiModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainMapOfFibreCocyclePairingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cochain_map_of_fibre_cocycle_pairing : ∀ (q N : ℕ) (i₁ i₂ i : ℤ) (h : i₁ + i₂ = i) (d : ℕ) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) (2 * (d : ℤ))), ∃ ψ : Cocycle (res (ZMod q) (tw q i₁)) (Jcx (ZMod q) q N (res (ZMod q) (tw q i))) (2 * (d : ℤ)), ∀ (m w : ℤ) (hw : m + 2 * (d : ℤ) = w) (U : Scheme.{0}) (a : Sec ((res (ZMod q) (tw q i₁)).X m) U), ∃ c : Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) (res (ZMod q) (tw q i)) w, Sec.map (ψ.1.v m w hw) a = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + w = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev c k s hs V y = twCast h ((twPair q i₁ i₂).mul V m (-(k : ℤ) + 2 * (d : ℤ)) s (by omega) (Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U) a) (ev z.1 k (-(k : ℤ) + 2 * (d : ℤ)) rfl V (Sx.map prod.snd y))) := by
  first | (exact @GlobalTheory.EtC.PsiModel.psi_exists) | (exact GlobalTheory.EtC.PsiModel.psi_exists) | (intros; apply GlobalTheory.EtC.PsiModel.psi_exists  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductDiscreteSpaceFibreEqPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductDiscreteSpaceFibreEqPairing
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.DiscCup

theorem sub_zero_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval 0 N h = 𝟙 _ := by
    ext i; simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem map_fst_sub {F : PSh} {E' : Spc} {N : ℕ} {U : Scheme.{0}} (w : Sx (disc.obj F ⨯ E') N U) (l : ℕ) (h : 0 + l ≤ N) :
    (show F.obj (op U) from Sx.map (prod.fst : disc.obj F ⨯ E' ⟶ _) (w.sub 0 l h)) =
      (show F.obj (op U) from Sx.map (prod.fst : disc.obj F ⨯ E' ⟶ _) w) := by
  unfold Sx.map Sx.sub
  have h1 := (prod.fst : disc.obj F ⨯ E' ⟶ _).naturality (SimplexCategory.subinterval 0 l h).op
  have h2 := congrArg (fun φ => φ.app (op U)) h1
  simp only [NatTrans.comp_app] at h2
  exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) h2) w)

theorem ev_vanish {E : Spc} {R : Type} [CommRing R] {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (hv : α.v (-(p : ℤ)) s h = 0) (U : Scheme.{0}) (x : Sx E p U) : _root_.GlobalTheory.EtC.ev (R := R) α p s h U x = 0 := by
  rw [_root_.GlobalTheory.EtC.ev, hv, comp_zero]
  rfl

end GlobalTheory.EtC.DiscCup

namespace GlobalTheory.EtC.DiscCup

theorem term_zero {q : ℕ} {E₁ E₂ : Spc} {i₁ i₂ n m s : ℤ} (k : ℕ)
    (a : Cochain ((chains (ZMod q)).obj E₁) (res (ZMod q) (tw q i₁)) n)
    (b : Cochain ((chains (ZMod q)).obj E₂) (res (ZMod q) (tw q i₂)) m) (V : Scheme.{0})
    (p : ℕ) (hp : p = 0) (s₁ t₁ : ℤ) (hs₁ : -(p : ℤ) + n = s₁) (ht₁ : -((k - p : ℕ) : ℤ) + m = t₁) (hw : s₁ + t₁ = s)
    (x0 : Sx E₁ p V) (x1 : Sx E₂ (k - p) V) (y0 : Sx E₁ 0 V) (y1 : Sx E₂ k V)
    (h0 : ∀ e : p = 0, e ▸ x0 = y0) (h1 : ∀ e : k - p = k, e ▸ x1 = y1) (hs' : n + (-(k : ℤ) + m) = s) :
    (twPair q i₁ i₂).mul V s₁ t₁ s hw (_root_.GlobalTheory.EtC.ev (R := ZMod q) a p s₁ hs₁ V x0) (_root_.GlobalTheory.EtC.ev (R := ZMod q) b (k - p) t₁ ht₁ V x1) =
      (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s hs' (_root_.GlobalTheory.EtC.ev (R := ZMod q) a 0 n (by simp) V y0) (_root_.GlobalTheory.EtC.ev (R := ZMod q) b k (-(k : ℤ) + m) rfl V y1) := by
  subst hp
  have e0 := h0 rfl
  have e1 := h1 rfl
  subst e0 e1
  obtain rfl : s₁ = n := by omega
  subst ht₁
  rfl

end GlobalTheory.EtC.DiscCup

open GlobalTheory.EtC.DiscCup in
theorem GlobalTheory.EtC.disc_cup_fibre : ∀ (q N : ℕ) (F : PSh) {n m i₁ i₂ : ℤ} (α : Cocycle ((chains (ZMod q)).obj (disc.obj F)) (res (ZMod q) (tw q i₁)) n) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) m), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0) → ∃ γ : Cocycle ((chains (ZMod q)).obj (disc.obj F ⨯ fibQ q N)) (res (ZMod q) (tw q (i₁ + i₂))) (n + m), CohomologyClass.mk γ = cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk α)) (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk z)) ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + (n + m) = s) (V : Scheme.{0}) (w : Sx (disc.obj F ⨯ fibQ q N) k V), _root_.GlobalTheory.EtC.ev (R := ZMod q) γ.1 k s hs V w = (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s (by omega) (_root_.GlobalTheory.EtC.ev (R := ZMod q) α.1 0 n (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) w)) (_root_.GlobalTheory.EtC.ev (R := ZMod q) z.1 k (-(k : ℤ) + m) rfl V (Sx.map prod.snd w)) := by
  intro q N F n m i₁ i₂ α z hα
  let α' := zcomp (Cocycle.ofHom ((chains (ZMod q)).map (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _))) α (zero_add n)
  let z' := zcomp (Cocycle.ofHom ((chains (ZMod q)).map (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _))) z (zero_add m)
  obtain ⟨γ, hγ⟩ := (twPair q i₁ i₂).aw_exists (disc.obj F ⨯ fibQ q N) rfl α' z'
  refine ⟨γ, ((twPair q i₁ i₂).cup_spec _ rfl α' z' γ hγ).symm, ?_⟩
  intro k s hs V w
  rw [hγ k s hs V w, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · have e1 : ((m * (((0 : Fin (k + 1)) : ℕ) : ℤ)).negOnePow) = 1 := by simp
    rw [e1, one_smul]
    change (twPair q i₁ i₂).mul V _ _ s _ (_root_.GlobalTheory.EtC.ev (R := ZMod q) ((Cochain.ofHom _).comp α.1 (zero_add n)) _ _ rfl V _)
      (_root_.GlobalTheory.EtC.ev (R := ZMod q) ((Cochain.ofHom _).comp z.1 (zero_add m)) _ _ rfl V _) = _
    rw [CupSpec.ev_pull, CupSpec.ev_pull]
    apply term_zero k α.1 z.1 V _ (by simp)
    · intro e
      exact map_fst_sub w _ _
    · intro e
      exact congrArg (Sx.map prod.snd) (sub_zero_full w _)
  · intro i _
    change _ • (twPair q i₁ i₂).mul V _ _ s _ (_root_.GlobalTheory.EtC.ev (R := ZMod q) ((Cochain.ofHom _).comp α.1 (zero_add n)) _ _ rfl V _) _ = 0
    rw [CupSpec.ev_pull, ev_vanish α.1 (i.succ : ℕ) _ _ (hα _ (by simp) _ _), map_zero, LinearMap.zero_apply, smul_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductDiscreteSpaceFibreEqPairingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_discreteSpace_fibre_eq_pairing : ∀ (q N : ℕ) (F : PSh) {n m i₁ i₂ : ℤ} (α : Cocycle ((chains (ZMod q)).obj (disc.obj F)) (res (ZMod q) (tw q i₁)) n) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) m), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0) → ∃ γ : Cocycle ((chains (ZMod q)).obj (disc.obj F ⨯ fibQ q N)) (res (ZMod q) (tw q (i₁ + i₂))) (n + m), CohomologyClass.mk γ = cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk α)) (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk z)) ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + (n + m) = s) (V : Scheme.{0}) (w : Sx (disc.obj F ⨯ fibQ q N) k V), _root_.GlobalTheory.EtC.ev (R := ZMod q) γ.1 k s hs V w = (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s (by omega) (_root_.GlobalTheory.EtC.ev (R := ZMod q) α.1 0 n (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) w)) (_root_.GlobalTheory.EtC.ev (R := ZMod q) z.1 k (-(k : ℤ) + m) rfl V (Sx.map prod.snd w)) := by
  first | (exact @GlobalTheory.EtC.disc_cup_fibre) | (exact GlobalTheory.EtC.disc_cup_fibre) | (intros; apply GlobalTheory.EtC.disc_cup_fibre  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleModelCochainComplexIsStrictlyGE
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleModelCochainComplexIsStrictlyGE
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem cochain_chains_subsingleton {R : Type} [CommRing R] (E : Spc) (I : Cx R) (hI : I.IsStrictlyGE 0) (n : ℤ)
    (hn : n < 0) : Subsingleton (Cochain ((chains R).obj E) I n) := by
  constructor
  intro a b
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · have hz : IsZero (((chains R).obj E).X p) :=
      HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p (fun i hi => by
        change -(i : ℤ) = p at hi
        omega)
    exact hz.eq_of_src _ _
  · have hz : IsZero (I.X q) := I.isZero_of_isStrictlyGE 0 q (by omega)
    exact hz.eq_of_tgt _ _

theorem Jcx_isStrictlyGE (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (hI : I.IsStrictlyGE 0) :
    (Jcx R q N I).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have hpre : IsZero (cotPre R q N I n) := by
    refine Functor.isZero _ (fun U => ?_)
    have h := cochain_chains_subsingleton (sch.obj U.unop ⨯ fibQ q N) I hI n hn
    letI : Subsingleton ((cotPre R q N I n).obj U) := h
    exact ModuleCat.isZero_of_subsingleton _
  exact (presheafToSheaf Scheme.etaleTopology.{0} _).map_isZero hpre

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleModelCochainComplexIsStrictlyGEStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projBundleModelCochainComplex_isStrictlyGE : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), I.IsStrictlyGE 0 → (Jcx R q N I).IsStrictlyGE 0 := by
  first | (exact @GlobalTheory.EtC.Jcx_isStrictlyGE) | (exact GlobalTheory.EtC.Jcx_isStrictlyGE) | (intros; apply GlobalTheory.EtC.Jcx_isStrictlyGE  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoTrivialProjBundleProdFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoTrivialProjBundleProdFibre
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem comp_trivV (N : ℕ) {E E' : Spc} (f : E' ⟶ E) : f ≫ trivV N E = trivV N E' := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq rfl)

theorem hom_ext_invertibleLocus (q : ℕ) {E : Spc} (f g : E ⟶ disc.obj (invP q)) : f = g := by
  ext n U x
  exact Subsingleton.elim (α := PLift _) _ _

def toInvP (q : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) : disc.obj F ⟶ disc.obj (invP q) :=
  disc.map
    { app := fun U => TypeCat.ofHom fun x => ⟨hF U.unop ⟨x⟩⟩
      naturality := fun _ _ _ => by ext x; rfl }

def fibQ.snd (q N : ℕ) : fibQ q N ⟶ PGL N :=
  pullback.snd (trivV N (disc.obj (invP q))) (PGL.pr N)

theorem fibQ.cond (q N : ℕ) : trivV N (fibQ q N) = fibQ.snd q N ≫ PGL.pr N := by
  show trivV N (pullback (trivV N (disc.obj (invP q))) (PGL.pr N)) = pullback.snd _ _ ≫ PGL.pr N
  rw [← comp_trivV N (pullback.fst (trivV N (disc.obj (invP q))) (PGL.pr N))]
  exact pullback.condition

def fibQ.lift {q N : ℕ} {X : Spc} (a : X ⟶ disc.obj (invP q)) (b : X ⟶ PGL N) (h : trivV N X = b ≫ PGL.pr N) :
    X ⟶ fibQ q N :=
  pullback.lift a b (by rw [comp_trivV]; exact h)

@[simp] theorem fibQ.lift_snd {q N : ℕ} {X : Spc} (a : X ⟶ disc.obj (invP q)) (b : X ⟶ PGL N)
    (h : trivV N X = b ≫ PGL.pr N) : fibQ.lift a b h ≫ fibQ.snd q N = b :=
  pullback.lift_snd (f := trivV N (disc.obj (invP q))) (g := PGL.pr N) a b
    (by rw [comp_trivV]; exact h)

theorem fibQ.hom_ext {q N : ℕ} {X : Spc} {f g : X ⟶ fibQ q N} (h : f ≫ fibQ.snd q N = g ≫ fibQ.snd q N) : f = g :=
  pullback.hom_ext (hom_ext_invertibleLocus q _ _) h

theorem trivProj_iso (q N : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) :
    ∃ θ : disc.obj F ⨯ fibQ q N ≅ pullback (trivV N (disc.obj F)) (PGL.pr N),
      θ.hom ≫ pullback.fst _ _ = prod.fst ∧ θ.hom ≫ pullback.snd _ _ ≫ PGL.line N = prod.snd ≫ lineQ q N := by
  have h1 : prod.fst ≫ trivV N (disc.obj F) = (prod.snd ≫ fibQ.snd q N) ≫ PGL.pr N := by
    rw [comp_trivV, Category.assoc, ← fibQ.cond, comp_trivV]
  have h2 : trivV N (pullback (trivV N (disc.obj F)) (PGL.pr N)) = pullback.snd _ _ ≫ PGL.pr N := by
    rw [← comp_trivV N (pullback.fst (trivV N (disc.obj F)) (PGL.pr N))]
    exact pullback.condition
  let hom : disc.obj F ⨯ fibQ q N ⟶ pullback (trivV N (disc.obj F)) (PGL.pr N) :=
    pullback.lift prod.fst (prod.snd ≫ fibQ.snd q N) h1
  let inv : pullback (trivV N (disc.obj F)) (PGL.pr N) ⟶ disc.obj F ⨯ fibQ q N :=
    prod.lift (pullback.fst _ _) (fibQ.lift (pullback.fst _ _ ≫ toInvP q F hF) (pullback.snd _ _) h2)
  refine ⟨{ hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }, ?_, ?_⟩
  · apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, pullback.lift_fst, Category.id_comp]
    · apply fibQ.hom_ext
      rw [Category.assoc, Category.assoc, ← Category.assoc inv, prod.lift_snd, fibQ.lift_snd, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, prod.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, prod.lift_snd, fibQ.lift_snd, Category.id_comp]
  · exact pullback.lift_fst _ _ _
  · rw [← Category.assoc, pullback.lift_snd, Category.assoc]
    rfl

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoTrivialProjBundleProdFibreStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_trivialProjBundle_prod_fibre : ∀ (q N : ℕ) (F : PSh), Inv q (disc.obj F) → ∃ θ : disc.obj F ⨯ fibQ q N ≅ pullback (trivV N (disc.obj F)) (PGL.pr N), θ.hom ≫ pullback.fst _ _ = prod.fst ∧ θ.hom ≫ pullback.snd _ _ ≫ PGL.line N = prod.snd ≫ lineQ q N := by
  first | (exact @GlobalTheory.EtC.trivProj_iso) | (exact GlobalTheory.EtC.trivProj_iso) | (intros; apply GlobalTheory.EtC.trivProj_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProjBundleFormulaMapOfFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProjBundleFormulaMapOfFactor
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PbfNatl

theorem pull_htCast' (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem pull_cpow' (q : ℕ) [NeZero q] (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x : Ht q E 2 1) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_htCast', (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_htCast', (hA q).1, ih]

theorem pull_pbfMap_of_factor : DivisorNaturality → ∀ (q : ℕ) [NeZero q] {E B P : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N))
    (L : B ⟶ ofCat (glCat 1)) (θ : P ⟶ pullback V (PGL.pr N)) (f : P ⟶ E) (g : P ⟶ B), Inv q B →
    Inv q (pullback V (PGL.pr N)) → θ ≫ pullback.fst _ _ = f → θ ≫ pullback.snd _ _ ≫ PGL.line N = g ≫ L →
    ∀ (n i : ℤ) (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))),
    pull _ θ _ _ (pbfMap q V n i a) = ∑ j : Fin N, ((cup q (pull _ f _ _ (a j)) (pull _ g _ _ (cpow q (c1 q L) j))).cast (by ring) (by ring) : Ht q P n i) := by
  intro hA q _ E B P N V L θ f g hB hP hf hg n i a
  unfold pbfMap
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_htCast', (hA q).1, ← pull_comp, hf, pull_cpow' q hA _ hP, (hA q).2.2.1 _ _ hP,
    pull_cpow' q hA _ hB, (hA q).2.2.1 _ _ hB, hg]

end GlobalTheory.EtC.PbfNatl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProjBundleFormulaMapOfFactorStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_projBundleFormulaMap_of_factor : DivisorNaturality → ∀ (q : ℕ) [NeZero q] {E B P : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (L : B ⟶ ofCat (glCat 1)) (θ : P ⟶ pullback V (PGL.pr N)) (f : P ⟶ E) (g : P ⟶ B), Inv q B → Inv q (pullback V (PGL.pr N)) → θ ≫ pullback.fst _ _ = f → θ ≫ pullback.snd _ _ ≫ PGL.line N = g ≫ L → ∀ (n i : ℤ) (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))), pull _ θ _ _ (pbfMap q V n i a) = ∑ j : Fin N, ((cup q (pull _ f _ _ (a j)) (pull _ g _ _ (cpow q (c1 q L) j))).cast (by ring) (by ring) : Ht q P n i) := by
  first | (exact @GlobalTheory.EtC.PbfNatl.pull_pbfMap_of_factor) | (exact GlobalTheory.EtC.PbfNatl.pull_pbfMap_of_factor) | (intros; apply GlobalTheory.EtC.PbfNatl.pull_pbfMap_of_factor  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveCochainModelTrivialProjectiveBund
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC

theorem inv_fibQ (q N : ℕ) : Inv q (fibQ q N) := fun U ⟨x⟩ =>
  (show (invP q).obj (op U) from Sx.map (pullback.fst (trivV N (disc.obj (invP q))) (PGL.pr N)) x).down

theorem inv_pullback_disc (q N : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) :
    Inv q (pullback (trivV N (disc.obj F)) (PGL.pr N)) := fun U ⟨x⟩ =>
  hF U ⟨Sx.map (pullback.fst (trivV N (disc.obj F)) (PGL.pr N)) x⟩

section
variable {q : ℕ}

theorem ev_comp_cochain {E : Spc} {I K : Cx (ZMod q)} {n d w : ℤ} (α : Cochain ((chains (ZMod q)).obj E) I n)
    (ψ : Cochain I K d) (h : n + d = w) (p : ℕ) (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + w = t)
    (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := ZMod q) (α.comp ψ h) p t ht U x = Sec.map (ψ.v s t (by omega)) (ev (R := ZMod q) α p s hs U x) := by
  rw [ev_def, ev_def, Cochain.comp_v α ψ h _ s t hs (by omega)]
  rfl

theorem cast_cocycle {E : Spc} {n n' i i' : ℤ} (hn : n' = n) (hi : i' = i)
    (γ : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i')) n') :
    ∃ γ' : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n,
      (CohomologyClass.mk γ' : Ht q E n i) = Ht.cast hn hi (CohomologyClass.mk γ) ∧
      ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0}) (w : Sx E k V),
        ev (R := ZMod q) γ'.1 k s hs V w = twCast hi (ev (R := ZMod q) γ.1 k s (by omega) V w) := by
  subst hn hi
  exact ⟨γ, rfl, fun _ _ _ _ _ => rfl⟩

theorem sxmap_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    Sx.map g (Sx.map f x) = Sx.map (f ≫ g) x := rfl

theorem coe_cocycle_sum {K L : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cocycle K L n) :
    ((∑ j ∈ t, c j : Cocycle K L n) : Cochain K L n) = ∑ j ∈ t, (c j : Cochain K L n) :=
  map_sum (AddMonoidHom.mk' (fun c : Cocycle K L n => (c : Cochain K L n)) (fun _ _ => rfl)) c t

theorem cochain_sum_v {K L : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cochain K L n) (p p' : ℤ)
    (h : p + n = p') : (∑ j ∈ t, c j).v p p' h = ∑ j ∈ t, (c j).v p p' h :=
  map_sum (AddMonoidHom.mk' (fun c : Cochain K L n => c.v p p' h) (fun a b => Cochain.add_v a b p p' h)) c t

theorem Jsec_sum {N : ℕ} {I : Cx (ZMod q)} {n : ℤ} {U : Scheme.{0}} {ι : Type} (t : Finset ι)
    (c : ι → Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) I n) : Jsec (∑ j ∈ t, c j) = ∑ j ∈ t, Jsec (c j) :=
  map_sum ((toSheafify Scheme.etaleTopology.{0} (cotPre (ZMod q) q N I n)).app (op U)).hom c t

theorem ev_cocycle_sum {E : Spc} {I : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cocycle ((chains (ZMod q)).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := ZMod q) (↑(∑ j ∈ t, c j) : Cochain _ _ _) p s h U x = ∑ j ∈ t, ev (R := ZMod q) (c j).1 p s h U x := by
  rw [coe_cocycle_sum]
  exact map_sum (evHom I n p s h U x) _ t

theorem ev_cochain_sum {E : Spc} {I : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cochain ((chains (ZMod q)).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := ZMod q) (∑ j ∈ t, c j) p s h U x = ∑ j ∈ t, ev (R := ZMod q) (c j) p s h U x :=
  map_sum (evHom I n p s h U x) c t

end

theorem pbf_disc_model : ∀ (q : ℕ) [NeZero q] (N : ℕ) (i : ℤ), ∃ (J : Cx (ZMod q)) (ψ : ∀ j : Fin N, Cocycle (res (ZMod q) (tw q (i - (j : ℕ)))) J (2 * (j : ℕ))), J.IsStrictlyGE 0 ∧ (∀ n, CategoryTheory.Injective (J.X n)) ∧ ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, ∃ e : CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) J n ≃+ Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i, ∀ a : ∀ j : Fin N, Ht q (disc.obj F) (n - 2 * (j : ℕ)) (i - (j : ℕ)), e (∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) = pbfMap q (trivV N (disc.obj F)) n i a := by
  intro q _ N i
  have hz : ∀ j : Fin N, ∃ z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q ((j : ℕ) : ℤ)))
      (2 * ((j : ℕ) : ℤ)), CohomologyClass.mk z = cpow q (c1 q (lineQ q N)) (j : ℕ) :=
    fun j => (cpow q (c1 q (lineQ q N)) (j : ℕ)).mk_surjective
  choose z hz using hz
  have hψ := fun j : Fin N => GlobalTheory.T.exists_cochain_map_of_fibre_cocycle_pairing q N (i - (j : ℕ)) (j : ℕ) i (by ring) (j : ℕ) (z j)
  choose ψ hψ using hψ
  refine ⟨Jcx (ZMod q) q N (res (ZMod q) (tw q i)), ψ,
    GlobalTheory.T.projBundleModelCochainComplex_isStrictlyGE _ q N _ (inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsStrictlyGE 0)),
    GlobalTheory.T.injective_projBundleModelCochainComplex_X _ q N _ (fun m => inferInstanceAs (Injective ((injectiveResolution (tw q i)).cochainComplex.X m))), ?_⟩
  intro F hF n
  obtain ⟨θ, hθ1, hθ2⟩ := GlobalTheory.T.exists_iso_trivialProjBundle_prod_fibre q N F hF
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre (ZMod q) q N (res (ZMod q) (tw q i)) F n
  let e₁ : Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i ≃+ Ht q (disc.obj F ⨯ fibQ q N) n i :=
    { toFun := pull _ θ.hom _ _
      invFun := pull _ θ.inv _ _
      left_inv := fun x => by rw [← pull_comp, θ.inv_hom_id, pull_id]
      right_inv := fun x => by rw [← pull_comp, θ.hom_inv_id, pull_id]
      map_add' := map_add _ }
  refine ⟨e₀.trans e₁.symm, fun a => ?_⟩
  rw [AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  change e₀ _ = pull _ θ.hom _ _ (pbfMap q (trivV N (disc.obj F)) n i a)
  rw [GlobalTheory.T.pullback_projBundleFormulaMap_of_factor GlobalTheory.T.cup_chern_kummer_pullback_naturality q (trivV N (disc.obj F)) (lineQ q N) θ.hom prod.fst prod.snd (inv_fibQ q N)
    (inv_pullback_disc q N F hF) hθ1 hθ2 n i a]
  have hα := fun j : Fin N => GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos (ZMod q) F (res (ZMod q) (tw q (i - (j : ℕ)))) (n - 2 * ((j : ℕ) : ℤ)) (a j)
  choose α hαa hα0 using hα
  have hγ := fun j : Fin N => GlobalTheory.T.cupProduct_discreteSpace_fibre_eq_pairing q N F (α j) (z j) (hα0 j)
  choose γ hγc hγv using hγ
  have hγ' := fun j : Fin N => cast_cocycle (q := q) (E := disc.obj F ⨯ fibQ q N)
    (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) (show i - ((j : ℕ) : ℤ) + ((j : ℕ) : ℤ) = i by ring) (γ j)
  choose γ' hγ'c hγ'v using hγ'
  let mkH : ∀ {K L : Cx (ZMod q)} {m : ℤ}, Cocycle K L m →+ CohomologyClass K L m :=
    fun {K L m} => AddMonoidHom.mk' CohomologyClass.mk CohomologyClass.mk_add
  have hL : (∑ j, cpost _ (ψ j) (n - 2 * ((j : ℕ) : ℤ)) n (by omega) (a j)) =
      CohomologyClass.mk (∑ j, zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show CohomologyClass.mk (∑ j, zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)) =
      mkH (∑ j, zcomp (α j) (ψ j) _) from rfl, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hαa j]
    rfl
  have hR : (∑ j : Fin N, ((cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (a j))
      (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (cpow q (c1 q (lineQ q N)) j))).cast (by ring) (by ring) :
        Ht q _ n i)) = CohomologyClass.mk (∑ j, γ' j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show CohomologyClass.mk (∑ j, γ' j) = mkH (∑ j, γ' j) from rfl, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = CohomologyClass.mk (γ' j)
    rw [hγ'c j, hγc j, hαa j, hz j]
  rw [hL, hR]
  apply he₀
  · intro p hp s h
    have key : ∀ j : Fin N, (zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)).1.v
        (-(p : ℤ)) s h = 0 := fun j => by
      rw [show (zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)).1 =
        (α j).1.comp (ψ j).1 (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) from rfl]
      rw [Cochain.comp_v _ _ _ _ (-(p : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) s rfl (by omega), hα0 j p hp _ rfl, zero_comp]
    rw [coe_cocycle_sum, cochain_sum_v]
    exact Finset.sum_eq_zero fun j _ => key j
  · intro U x
    have hc := fun j : Fin N => hψ j (n - 2 * ((j : ℕ) : ℤ)) n (by ring) U (ev (R := ZMod q) (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) U x)
    choose c hc1 hc2 using hc
    refine ⟨∑ j, c j, ?_, ?_⟩
    · rw [ev_cocycle_sum, Jsec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc1 j]
      exact ev_comp_cochain (α j).1 (ψ j).1 (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) 0 _ n (by simp) (by simp) U x
    · intro k s hs V y
      rw [ev_cochain_sum, ev_cocycle_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc2 j, hγ'v j, hγv j]
      have e2 : Sx.map (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _)
          (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y) = Sx.map prod.snd y :=
        (sxmap_comp (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) prod.snd y).trans
          (by rw [prod.map_snd, Category.comp_id]; rfl)
      have e1 : (Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _)
          (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y) : F.obj (op V)) =
          F.map (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U).op x :=
        (sxmap_comp (E := disc.obj (yoneda.obj U) ⨯ fibQ q N) _ _ y).trans (by
          rw [prod.map_fst]
          rfl)
      have e3 : Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U)
          (ev (R := ZMod q) (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) U x) =
          ev (R := ZMod q) (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k)
            (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) :=
        (ev_res _ _ _ _ _ _).trans (congrArg _ e1.symm)
      rw [e2, e3]

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveCochainModelTrivialProjectiveBundStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_cochainModel_trivialProjectiveBundle : ∀ (q : ℕ) [NeZero q] (N : ℕ) (i : ℤ), ∃ (J : Cx (ZMod q)) (ψ : ∀ j : Fin N, Cocycle (res (ZMod q) (tw q (i - (j : ℕ)))) J (2 * (j : ℕ))), J.IsStrictlyGE 0 ∧ (∀ n, CategoryTheory.Injective (J.X n)) ∧ ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, ∃ e : CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) J n ≃+ Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i, ∀ a : ∀ j : Fin N, Ht q (disc.obj F) (n - 2 * (j : ℕ)) (i - (j : ℕ)), e (∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) = pbfMap q (trivV N (disc.obj F)) n i a := by
  first | (exact @GlobalTheory.EtC.pbf_disc_model) | (exact GlobalTheory.EtC.pbf_disc_model) | (intros; apply GlobalTheory.EtC.pbf_disc_model  <;> assumption)
end
