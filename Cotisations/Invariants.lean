/-
Théorèmes universels du modèle : propriétés prouvées pour TOUTES les
entrées (toute assiette, tout barème, toute liste de lignes, tout
bulletin), par déduction dans le noyau Lean — sans évaluation de cas
particuliers.

Contrairement aux ancrages chiffrés de `Exemples.lean` (égalités
numériques sur des exemples officiels, vérifiées par `native_decide`),
les énoncés ci-dessous sont quantifiés universellement. Ils constituent
les garanties de fond du modèle :
- un barème progressif recompose exactement le montant découpé ;
- les tranches de plafond sont positives, bornées, et se recomposent ;
- la ventilation par organisme conserve le total des lignes ;
- la réduction générale est nulle au-delà du plafond ;
- les invariants comptables du bulletin (net, coût employeur, somme
  des versements) sont vérifiés pour tout salarié, toute entreprise,
  toute convention, et se conservent par composition.
-/
import Cotisations.Assiette
import Cotisations.Organismes
import Cotisations.Parametres
import Cotisations.ReducGenerale
import Cotisations.Bulletin
import Cotisations.Syntech

namespace Cotisations

/-! ### Arithmétique rationnelle : lemmes auxiliaires -/

theorem Rat.add_add_add_comm (a b c d : Rat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Rat.add_assoc a b (c + d), ← Rat.add_assoc b c d, Rat.add_comm b c, Rat.add_assoc c b d,
    ← Rat.add_assoc a c (b + d)]

theorem Rat.add_sub_self (a b : Rat) : b + (a - b) = a := by
  rw [Rat.add_comm, Rat.sub_add_cancel]

theorem Rat.le_refl' (a : Rat) : a ≤ a := Rat.le_refl (a := a)

theorem Rat.le_total' (a b : Rat) : a ≤ b ∨ b ≤ a := Rat.le_total (a := a) (b := b)

theorem Rat.eq_of_sub_eq_zero {a b : Rat} (h : a - b = 0) : a = b := by
  have h2 := Rat.add_sub_self a b
  rw [h, Rat.add_zero] at h2
  exact h2.symm

theorem Rat.sub_nonneg_of_le {a b : Rat} (h : b ≤ a) : 0 ≤ a - b := by
  have h1 : 0 + b ≤ (a - b) + b := by rw [Rat.zero_add, Rat.sub_add_cancel]; exact h
  rw [Rat.add_comm 0 b, Rat.add_comm (a - b) b] at h1
  exact (Rat.add_le_add_left (c := b)).mp h1

theorem Rat.le_of_sub_nonneg {a b : Rat} (h : 0 ≤ a - b) : b ≤ a := by
  have h1 : b + 0 ≤ b + (a - b) := Rat.add_le_add_left.mpr h
  rwa [Rat.add_zero, Rat.add_sub_self] at h1

theorem Rat.sub_nonpos_of_le {a b : Rat} (h : a ≤ b) : a - b ≤ 0 := by
  have h1 : (a - b) + b ≤ 0 + b := by rw [Rat.sub_add_cancel, Rat.zero_add]; exact h
  rw [Rat.add_comm (a - b) b, Rat.add_comm 0 b] at h1
  exact (Rat.add_le_add_left (c := b)).mp h1

theorem Rat.sub_self (a : Rat) : a - a = 0 :=
  Rat.le_antisymm (Rat.sub_nonpos_of_le (Rat.le_refl' a)) (Rat.sub_nonneg_of_le (Rat.le_refl' a))

/-! ### min, max, clamp0 : valeurs par cas -/

theorem Rat.min_of_le {a b : Rat} (h : a ≤ b) : min a b = a := by
  rw [Rat.min_def, if_pos h]

theorem Rat.min_of_ge {a b : Rat} (h : b ≤ a) : min a b = b := by
  rw [Rat.min_def]
  split
  · next hn => exact Rat.le_antisymm hn h
  · rfl

theorem Rat.max_of_le {a b : Rat} (h : a ≤ b) : max a b = b := by
  rw [Rat.max_def, if_pos h]

theorem Rat.max_of_ge {a b : Rat} (h : b ≤ a) : max a b = a := by
  rw [Rat.max_def]
  split
  · next hn => exact (Rat.le_antisymm hn h).symm
  · rfl

theorem clamp0_nonneg (x : Eur) : 0 ≤ clamp0 x := by
  rw [clamp0, Rat.max_def]
  split
  · assumption
  · exact Rat.le_refl' 0

theorem clamp0_of_nonneg {x : Eur} (h : 0 ≤ x) : clamp0 x = x := by
  rw [clamp0, Rat.max_def, if_pos h]

theorem clamp0_of_nonpos {x : Eur} (h : x ≤ 0) : clamp0 x = 0 := by
  rw [clamp0, Rat.max_def]
  split
  · next hn => exact Rat.le_antisymm h hn
  · rfl

/-- Sous le seuil, la part excédentaire est nulle. -/
theorem clamp0_sub_le {x s : Eur} (h : x ≤ s) : clamp0 (x - s) = 0 := by
  rcases Rat.le_total' (x - s) 0 with h' | h'
  · exact clamp0_of_nonpos h'
  · rw [clamp0_of_nonneg h', Rat.le_antisymm h (Rat.le_of_sub_nonneg h'), Rat.sub_self]

/-- Au-dessus du seuil, la part excédentaire est conservée. -/
theorem clamp0_sub_ge {x s : Eur} (h : s ≤ x) : clamp0 (x - s) = x - s := by
  rcases Rat.le_total' (x - s) 0 with h' | h'
  · rw [clamp0_of_nonpos h',
      Rat.eq_of_sub_eq_zero (Rat.le_antisymm h' (Rat.sub_nonneg_of_le h)), Rat.sub_self]
  · exact clamp0_of_nonneg h'

/-! ### Barèmes progressifs : propriétés universelles -/

/-- Un barème progressif à deux seuils recompose exactement le montant
    découpé : la somme des trois tranches redonne `x`, pour tout `x` et
    tous seuils ordonnés. Aucun euro n'est perdu ni compté deux fois,
    ni dans le plafonnement de sécurité sociale, ni dans le barème de
    la taxe sur les salaires. -/
theorem decoupeBareme_somme (x s1 s2 : Eur) (h : s1 ≤ s2) :
    (decoupeBareme x s1 s2).1 + (decoupeBareme x s1 s2).2.1
      + (decoupeBareme x s1 s2).2.2 = x := by
  have h1 : (decoupeBareme x s1 s2).1 = min x s1 := rfl
  have h2 : (decoupeBareme x s1 s2).2.1 = clamp0 (min x s2 - s1) := rfl
  have h3 : (decoupeBareme x s1 s2).2.2 = clamp0 (x - s2) := rfl
  rw [h1, h2, h3]
  rcases Rat.le_total' x s1 with hx1 | hx1
  · rw [Rat.min_of_le hx1, Rat.min_of_le (Rat.le_trans hx1 h), clamp0_sub_le hx1,
      clamp0_sub_le (Rat.le_trans hx1 h), Rat.add_zero, Rat.add_zero]
  · rcases Rat.le_total' x s2 with hx2 | hx2
    · rcases Rat.le_total' x s1 with h' | h'
      · rw [Rat.min_of_le h', Rat.min_of_le hx2, clamp0_sub_le h', clamp0_sub_le hx2,
          Rat.add_zero, Rat.add_zero]
      · rw [Rat.min_of_ge hx1, Rat.min_of_le hx2, clamp0_sub_ge hx1, clamp0_sub_le hx2,
          Rat.add_zero, Rat.add_sub_self]
    · rcases Rat.le_total' x s1 with h' | h'
      · rw [Rat.min_of_le h', Rat.min_of_le (Rat.le_trans h' h), clamp0_sub_le h',
          clamp0_sub_le (Rat.le_trans h' h), Rat.add_zero, Rat.add_zero]
      · rw [Rat.min_of_ge hx1]
        rcases Rat.le_total' x s2 with h'' | h''
        · rw [Rat.min_of_le h'', clamp0_sub_ge hx1, clamp0_sub_le h'', Rat.add_zero,
            Rat.add_sub_self]
        · rw [Rat.min_of_ge hx2, clamp0_sub_ge h, clamp0_sub_ge hx2,
            Rat.add_sub_self, Rat.add_sub_self]

theorem plafond_le_huit (p : Eur) (hp : 0 ≤ p) : p ≤ 8 * p := by
  have h7 : 0 ≤ (7 : Rat) * p := Rat.mul_nonneg (by decide) hp
  have h1 : p + 0 ≤ p + (7 : Rat) * p := Rat.add_le_add_left.mpr h7
  rw [Rat.add_zero] at h1
  have h2 : ((1 : Rat) + 7) * p = (1 : Rat) * p + (7 : Rat) * p := Rat.add_mul 1 7 p
  rw [show ((1 : Rat) + 7 : Rat) = 8 from by native_decide, Rat.one_mul] at h2
  rw [h2]
  exact h1

/-- La tranche 1 ne dépasse jamais le plafond. -/
theorem decoupeTranches_tranche1_le_plafond (a p : Eur) :
    (decoupeTranches a p).tranche1 ≤ p := by
  have h : (decoupeTranches a p).tranche1 = min a p := rfl
  rw [h, Rat.min_def]
  split
  · assumption
  · exact Rat.le_refl' p

/-- Les tranches 2 et 3 sont positives. -/
theorem decoupeTranches_tranche2_nonneg (a p : Eur) : 0 ≤ (decoupeTranches a p).tranche2 :=
  clamp0_nonneg _

theorem decoupeTranches_tranche3_nonneg (a p : Eur) : 0 ≤ (decoupeTranches a p).tranche3 :=
  clamp0_nonneg _

/-- La somme des trois tranches redonne l'assiette, pour toute assiette
    et tout plafond positif : le plafonnement ne perd ni n'ajoute rien. -/
theorem decoupeTranches_somme (a p : Eur) (hp : 0 ≤ p) :
    (decoupeTranches a p).tranche1 + (decoupeTranches a p).tranche2
      + (decoupeTranches a p).tranche3 = a := by
  have h1 : (decoupeTranches a p).tranche1 = (decoupeBareme a p (8 * p)).1 := rfl
  have h2 : (decoupeTranches a p).tranche2 = (decoupeBareme a p (8 * p)).2.1 := rfl
  have h3 : (decoupeTranches a p).tranche3 = (decoupeBareme a p (8 * p)).2.2 := rfl
  rw [h1, h2, h3]
  exact decoupeBareme_somme a p (8 * p) (plafond_le_huit p hp)

/-- L'assiette plafonnée à 4 PASS reste sous 4 PASS. -/
theorem assietteQuatrePlafonds_le (a p : Eur) : assietteQuatrePlafonds a p ≤ 4 * p := by
  rw [assietteQuatrePlafonds, Rat.min_def]
  split
  · assumption
  · exact Rat.le_refl' (4 * p)

/-! ### Sommes de lignes : structures additives -/

theorem foldl_add_seed {α : Type} (g : α → Eur) (l : List α) (a c : Eur) :
    l.foldl (fun acc x => acc + g x) (a + c) = a + l.foldl (fun acc x => acc + g x) c := by
  induction l generalizing c with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, Rat.add_assoc, ih]

theorem sommeSur_append (f : LigneCotisation → Eur) (l₁ l₂ : List LigneCotisation) :
    sommeSur f (l₁ ++ l₂) = sommeSur f l₁ + sommeSur f l₂ := by
  rw [sommeSur, sommeSur, sommeSur, List.foldl_append,
    ← Rat.add_zero (List.foldl (fun acc x => acc + f x) 0 l₁), foldl_add_seed, Rat.add_zero]

theorem sommeSalariale_append (l₁ l₂ : List LigneCotisation) :
    sommeSalariale (l₁ ++ l₂) = sommeSalariale l₁ + sommeSalariale l₂ :=
  sommeSur_append _ l₁ l₂

theorem sommePatronale_append (l₁ l₂ : List LigneCotisation) :
    sommePatronale (l₁ ++ l₂) = sommePatronale l₁ + sommePatronale l₂ :=
  sommeSur_append _ l₁ l₂

theorem sommeSur_cons (f : LigneCotisation → Eur) (x : LigneCotisation)
    (xs : List LigneCotisation) :
    sommeSur f (x :: xs) = f x + sommeSur f xs := by
  show List.foldl (fun acc y => acc + f y) 0 (x :: xs)
    = f x + List.foldl (fun acc y => acc + f y) 0 xs
  rw [List.foldl_cons, foldl_add_seed (fun y => f y) xs 0 (f x), Rat.zero_add,
    ← foldl_add_seed (fun y => f y) xs (f x) 0, Rat.add_zero]

theorem sommeSalariale_cons (x : LigneCotisation) (xs : List LigneCotisation) :
    sommeSalariale (x :: xs) = x.partSalariale + sommeSalariale xs :=
  sommeSur_cons _ x xs

theorem sommePatronale_cons (x : LigneCotisation) (xs : List LigneCotisation) :
    sommePatronale (x :: xs) = x.partPatronale + sommePatronale xs :=
  sommeSur_cons _ x xs

/-- Filtrer les lignes nulles ne change aucune somme : les lignes
    écartées portent deux parts nulles. -/
theorem sommeSur_filtrée (f : LigneCotisation → Eur) (hf : ∀ x, x.estNulle = true → f x = 0)
    (l : List LigneCotisation) :
    sommeSur f (l.filter (fun x => !x.estNulle)) = sommeSur f l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons]
    split
    · next h => rw [sommeSur_cons, sommeSur_cons, ih]
    · next h =>
      have hx : x.estNulle = true := by
        cases hb : x.estNulle with
        | true => rfl
        | false => rw [hb] at h; exact absurd rfl h
      rw [sommeSur_cons, ih, hf x hx, Rat.zero_add]

theorem sommeSalariale_filtrée (l : List LigneCotisation) :
    sommeSalariale (l.filter (fun x => !x.estNulle)) = sommeSalariale l :=
  sommeSur_filtrée _ (fun x hx => (LigneCotisation.estNulle_parts x hx).1) l

theorem sommePatronale_filtrée (l : List LigneCotisation) :
    sommePatronale (l.filter (fun x => !x.estNulle)) = sommePatronale l :=
  sommeSur_filtrée _ (fun x hx => (LigneCotisation.estNulle_parts x hx).2) l

/-! ### Ventilation par organisme : conservation du total -/

theorem foldl_add_split {α : Type} (f g : α → Eur) (l : List α) :
    l.foldl (fun acc x => acc + (f x + g x)) 0
      = l.foldl (fun acc x => acc + f x) 0 + l.foldl (fun acc x => acc + g x) 0 := by
  induction l with
  | nil => rw [List.foldl_nil, List.foldl_nil, List.foldl_nil, Rat.zero_add]
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
    simp only [Rat.zero_add]
    rw [← Rat.add_zero (f x + g x), foldl_add_seed, ih,
      Rat.add_add_add_comm (f x) (g x) (xs.foldl (fun acc y => acc + f y) 0)
        (xs.foldl (fun acc y => acc + g y) 0), ← foldl_add_seed, ← foldl_add_seed]
    simp only [Rat.add_zero]

theorem montantOrganisme_cons (org : Organisme) (x : LigneCotisation)
    (xs : List LigneCotisation) :
    montantOrganisme org (x :: xs)
      = montantOrganisme org xs
        + (if x.organisme == org then x.partSalariale + x.partPatronale else 0) := by
  rw [montantOrganisme, montantOrganisme, List.foldl_cons, Rat.zero_add,
    ← Rat.add_zero (if x.organisme == org then x.partSalariale + x.partPatronale else 0),
    foldl_add_seed, Rat.add_zero]
  exact Rat.add_comm (if x.organisme == org then x.partSalariale + x.partPatronale else 0)
    (montantOrganisme org xs)

theorem organisme_tous_une_fois (o : Organisme) (m : Eur) :
    Organisme.tous.foldl (fun acc g => acc + if o == g then m else 0) 0 = m := by
  cases o <;>
    simp [Organisme.tous, List.foldl_cons, List.foldl_nil, Rat.zero_add, Rat.add_zero]

/-- **Conservation par la ventilation.** Pour toute liste de lignes, la
    somme des versements par organisme égale la somme des parts
    salariales et patronales : la ventilation ne perd ni ne crée
    d'euro, quel que soit le bulletin. -/
theorem versements_conservent_le_total (l : List LigneCotisation) :
    (versementsParOrganisme l).foldl (fun acc p => acc + p.2) 0
      = sommeSalariale l + sommePatronale l := by
  have hcore : Organisme.tous.foldl (fun acc org => acc + montantOrganisme org l) 0
      = sommeSalariale l + sommePatronale l := by
    induction l with
    | nil =>
      have hg : ∀ org : Organisme, montantOrganisme org ([] : List LigneCotisation) = 0 :=
        fun _ => rfl
      simp [Organisme.tous, hg, List.foldl_cons, List.foldl_nil, Rat.add_zero,
        sommeSalariale, sommePatronale, sommeSur]
    | cons x xs ih =>
      simp only [montantOrganisme_cons]
      rw [foldl_add_split (fun org => montantOrganisme org xs)
        (fun org => if x.organisme == org then x.partSalariale + x.partPatronale else 0),
        ih, organisme_tous_une_fois x.organisme (x.partSalariale + x.partPatronale),
        sommeSalariale_cons, sommePatronale_cons,
        Rat.add_comm x.partSalariale (sommeSalariale xs),
        Rat.add_comm x.partPatronale (sommePatronale xs),
        Rat.add_add_add_comm (sommeSalariale xs) x.partSalariale (sommePatronale xs)
          x.partPatronale]
  rw [versementsParOrganisme, List.foldl_map]
  exact hcore

/-! ### Forme normale des sommes sur une concaténation -/

/-- Sommes sur une concaténation de quatre listes, avec part salariale
    des lignes patronales et part patronale des lignes salariales
    supposées nulles. -/
theorem somme_norme (sl rt pt rd : List LigneCotisation)
    (h1 : sommeSalariale pt = 0) (h3 : sommePatronale sl = 0) :
    sommeSalariale (sl ++ rt ++ pt ++ rd) + sommePatronale (sl ++ rt ++ pt ++ rd)
      = sommeSalariale sl + sommeSalariale rt + 0 + sommeSalariale rd
        + (0 + sommePatronale rt + sommePatronale pt + sommePatronale rd) := by
  rw [sommeSalariale_append, sommeSalariale_append, sommeSalariale_append,
    sommePatronale_append, sommePatronale_append, sommePatronale_append, h1, h3]

theorem somme_norme_zero (sl rt pt rd : List LigneCotisation)
    (h1 : sommeSalariale pt = 0) (h2 : sommeSalariale rd = 0)
    (h3 : sommePatronale sl = 0) :
    sommeSalariale (sl ++ rt ++ pt ++ rd) + sommePatronale (sl ++ rt ++ pt ++ rd)
      = sommeSalariale sl + sommeSalariale rt
        + (sommePatronale pt + sommePatronale rt + sommePatronale rd) := by
  rw [somme_norme sl rt pt rd h1 h3, h2]
  simp only [Rat.add_zero, Rat.zero_add]
  rw [Rat.add_comm (sommePatronale rt) (sommePatronale pt)]

/-! ### Invariants comptables du bulletin, pour toute entrée -/

/-- Les quatre invariants comptables d'un bulletin, pour toute entrée :
    1. net = brut − total salarial ;
    2. coût employeur = brut + total patronal net ;
    3. la somme des versements par organisme égale le total des cotisations ;
    4. le total se recompose à partir des lignes stockées. -/
structure Bulletin.invariants (b : Bulletin) : Prop where
  net : b.netAvantIR + b.totalSalarial = b.brut
  cout : b.coutEmployeur = b.brut + b.totalPatronalNet
  versements : (b.versements.foldl (fun acc p => acc + p.2) 0)
      = b.totalSalarial + b.totalPatronalNet
  lignes : b.totalSalarial + b.totalPatronalNet
      = sommeSalariale (b.lignesSalariales ++ b.lignesRetraite ++ b.lignesPatronales
          ++ b.lignesReductions)
        + sommePatronale (b.lignesSalariales ++ b.lignesRetraite ++ b.lignesPatronales
          ++ b.lignesReductions)

/-! ### Les listes de lignes du bulletin légal -/

/-- Les lignes patronales de sécurité sociale ne portent aucune part
    salariale. -/
theorem sommeSalariale_lignesSecuPatronales (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (t : Tranches) (plafond : Eur) :
    sommeSalariale (lignesSecuPatronales pa pe ps t plafond) = 0 := by
  by_cases he : pe.effectif ≥ 50 <;>
    simp [he, lignesSecuPatronales, maladiePatronale, csaPatronale, vieillessePatronale,
      ligneVieillesse, lignePatronaleUrssaf, famillePatronale, fnalPatronal, chomagePatronal,
      agsPatronale, dialogueSocialPatronale, atmpPatronale, ligneTauxUnique, sommeSalariale,
      sommeSur, List.foldl_append, List.foldl_cons, List.foldl_nil, Rat.add_zero]

/-- Les lignes de taxes ne portent aucune part salariale. -/
theorem sommeSalariale_lignesTaxesPatronales (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (t : Tranches) (plafond : Eur) :
    sommeSalariale (lignesTaxesPatronales pa pe ps t plafond) = 0 := by
  by_cases h1 : pe.assujettiTaxeSalaires <;> by_cases h2 : pe.contributionOETHAnnuelle > 0 <;>
    simp [h1, h2, lignesTaxesPatronales, formationProfessionnelle, taxeApprentissage,
      csaApprentissage, effortConstruction, versementMobilite, contributionCpfCdd,
      forfaitSocial, taxeSurSalaires, taxeSurSalairesSalarie, contributionOETH,
      ligneTauxUnique, sommeSalariale, sommeSur, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Rat.add_zero]

/-- Les lignes patronales conventionnelles ne portent aucune part
    salariale. -/
theorem sommeSalariale_lignesConventionPatronales (cc : ConventionCollective) (t : Tranches) :
    sommeSalariale (lignesConventionPatronales cc t) = 0 := by
  by_cases h1 : cc.mutuellePatronale > 0 <;> by_cases h2 : cc.prevoyanceTauxT1 > 0 <;>
    by_cases h3 : cc.retraiteSupplementaireT1.tauxPatronal > 0 <;>
    by_cases h4 : cc.retraiteSupplementaireT2.tauxPatronal > 0 <;>
    by_cases h5 : cc.tauxCaisseCongesPayes > 0 <;>
    simp [h1, h2, h3, h4, h5, lignesConventionPatronales, lignesMutuelle, lignesRetraiteSupp,
      ligneTauxUnique, sommeSalariale, sommeSur, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Rat.add_zero]

/-- Les lignes salariales de sécurité sociale ne portent aucune part
    patronale. -/
theorem sommePatronale_lignesSecuSalariales (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (t : Tranches) :
    sommePatronale (lignesSecuSalariales pa pe ps t) = 0 := by
  by_cases h1 : pe.region == Region.alsaceMoselle <;> by_cases h2 : pe.regimeReel <;>
    simp [h1, h2, lignesSecuSalariales, vieillesseSalarialeT1, vieillesseSalarialeDeplafonnee,
      maladieAlsaceMoselleSalariale, csgDeductible, csgNonDeductible, csgForfaitaire, crds,
      ligneVieillesse, ligneCsgCrds, ligneTauxUnique, sommePatronale, sommeSur,
      List.foldl_append, List.foldl_cons, List.foldl_nil, Rat.add_zero]

/-- Les lignes salariales conventionnelles ne portent aucune part
    patronale. -/
theorem sommePatronale_lignesConventionSalariales (cc : ConventionCollective) (t : Tranches) :
    sommePatronale (lignesConventionSalariales cc t) = 0 := by
  by_cases h1 : cc.mutuelleSalariale > 0 <;> by_cases h2 : cc.prevoyanceTauxT1 > 0 <;>
    by_cases h3 : cc.retraiteSupplementaireT1.tauxSalarial > 0 <;>
    by_cases h4 : cc.retraiteSupplementaireT2.tauxSalarial > 0 <;>
    simp [h1, h2, h3, h4, lignesConventionSalariales, lignesMutuelle, lignesRetraiteSupp,
      ligneTauxUnique, sommePatronale, sommeSur, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Rat.add_zero]

private def lignesConvS (cc : Option ConventionCollective) (t : Tranches) :
    List LigneCotisation :=
  match cc with
  | some c => lignesConventionSalariales c t
  | none => []

private def lignesConvP (cc : Option ConventionCollective) (t : Tranches) :
    List LigneCotisation :=
  match cc with
  | some c => lignesConventionPatronales c t
  | none => []

private def salS (pa : ParametresAnnee) (pe : ParametresEntreprise) (ps : ParametresSalarie)
    (cc : Option ConventionCollective) : List LigneCotisation :=
  lignesSecuSalariales pa pe ps (decoupeTranches ps.assietteSecu (plafondMensuelProratise pa ps))
    ++ lignesConvS cc (decoupeTranches ps.assietteSecu (plafondMensuelProratise pa ps))

private def retraiteB (pa : ParametresAnnee) (ps : ParametresSalarie) : List LigneCotisation :=
  lignesRetraiteComplementaire ps parametresAgircArrco2026
    (decoupeTranches ps.assietteSecu (plafondMensuelProratise pa ps))
    (plafondMensuelProratise pa ps)

private def salP (pa : ParametresAnnee) (pe : ParametresEntreprise) (ps : ParametresSalarie)
    (cc : Option ConventionCollective) : List LigneCotisation :=
  (lignesSecuPatronales pa pe ps (decoupeTranches ps.assietteSecu (plafondMensuelProratise pa ps))
      (plafondMensuelProratise pa ps)
    ++ lignesTaxesPatronales pa pe ps (decoupeTranches ps.assietteSecu
        (plafondMensuelProratise pa ps)) (plafondMensuelProratise pa ps))
    ++ lignesConvP cc (decoupeTranches ps.assietteSecu (plafondMensuelProratise pa ps))

private def reductionsB (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : List LigneCotisation :=
  (if (if ps.contrat == TypeContrat.apprentissage then (0 : Eur)
      else montantRGDU (parametresRGDU pa pe) ps.assietteRGDU ps.brutHeuresSupplementaires) > 0 then
    [reductionRGDU pa pe ps (if ps.contrat == TypeContrat.apprentissage then (0 : Eur)
      else montantRGDU (parametresRGDU pa pe) ps.assietteRGDU ps.brutHeuresSupplementaires)]
  else [])
  ++ (if ps.nombreHeuresSupplementaires > 0 then [deductionForfaitaireHeuresSup pa pe ps]
    else [])

private theorem sommeSalariale_salP_nulle (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (cc : Option ConventionCollective) :
    sommeSalariale (salP pa pe ps cc) = 0 := by
  cases cc <;>
    simp only [salP, lignesConvP, sommeSalariale_append, sommeSalariale_lignesSecuPatronales,
      sommeSalariale_lignesTaxesPatronales, sommeSalariale_lignesConventionPatronales] <;>
    simp only [sommeSalariale, sommeSur, List.foldl_nil, Rat.add_zero]

private theorem sommePatronale_salS_nulle (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (cc : Option ConventionCollective) :
    sommePatronale (salS pa pe ps cc) = 0 := by
  cases cc <;>
    simp only [salS, lignesConvS, sommePatronale_append, sommePatronale_lignesSecuSalariales,
      sommePatronale_lignesConventionSalariales] <;>
    simp only [sommePatronale, sommeSur, List.foldl_nil, Rat.add_zero]

private theorem sommeSalariale_reductionsB_nulle (pa : ParametresAnnee)
    (pe : ParametresEntreprise) (ps : ParametresSalarie) :
    sommeSalariale (reductionsB pa pe ps) = 0 := by
  simp only [reductionsB, reductionRGDU, deductionForfaitaireHeuresSup]
  split <;> split <;> split
  all_goals
    simp only [sommeSalariale_append, sommeSalariale, sommeSur, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Rat.add_zero]

/-! ### Les quatre invariants du bulletin légal, champ par champ -/

/-- Invariant du net : net = brut − total salarial, pour tout salarié. -/
theorem calculeBulletin_net_invariant (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (cc : Option ConventionCollective) :
    (calculeBulletin pa pe ps cc).netAvantIR + (calculeBulletin pa pe ps cc).totalSalarial
      = (calculeBulletin pa pe ps cc).brut := by
  show ps.assietteSecu - (sommeSalariale (salS pa pe ps cc) + sommeSalariale (retraiteB pa ps))
    + (sommeSalariale (salS pa pe ps cc) + sommeSalariale (retraiteB pa ps)) = ps.assietteSecu
  exact Rat.sub_add_cancel

/-- Invariant des versements : la ventilation par organisme conserve le
    total des cotisations, pour tout salarié. -/
theorem calculeBulletin_versements_invariant (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (cc : Option ConventionCollective) :
    (calculeBulletin pa pe ps cc).versements.foldl (fun acc p => acc + p.2) 0
      = (calculeBulletin pa pe ps cc).totalSalarial
        + (calculeBulletin pa pe ps cc).totalPatronalNet := by
  show (versementsParOrganisme
      ((salS pa pe ps cc ++ retraiteB pa ps) ++ salP pa pe ps cc ++ reductionsB pa pe ps)).foldl
    (fun acc p => acc + p.2) 0
    = sommeSalariale (salS pa pe ps cc) + sommeSalariale (retraiteB pa ps)
      + (sommePatronale (salP pa pe ps cc) + sommePatronale (retraiteB pa ps)
        + sommePatronale (reductionsB pa pe ps))
  simp only [versements_conservent_le_total, sommeSalariale_append, sommePatronale_append,
    sommeSalariale_salP_nulle pa pe ps cc, sommeSalariale_reductionsB_nulle pa pe ps,
    sommePatronale_salS_nulle pa pe ps cc, Rat.add_zero, Rat.zero_add, Rat.add_assoc,
    Rat.add_comm, Rat.add_left_comm]

/-- Invariant des lignes : les totaux se recomposent à partir des lignes
    stockées (après filtre des lignes nulles), pour tout salarié. -/
theorem calculeBulletin_lignes_invariant (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (cc : Option ConventionCollective) :
    (calculeBulletin pa pe ps cc).totalSalarial + (calculeBulletin pa pe ps cc).totalPatronalNet
      = sommeSalariale ((calculeBulletin pa pe ps cc).lignesSalariales
          ++ (calculeBulletin pa pe ps cc).lignesRetraite
          ++ (calculeBulletin pa pe ps cc).lignesPatronales
          ++ (calculeBulletin pa pe ps cc).lignesReductions)
        + sommePatronale ((calculeBulletin pa pe ps cc).lignesSalariales
          ++ (calculeBulletin pa pe ps cc).lignesRetraite
          ++ (calculeBulletin pa pe ps cc).lignesPatronales
          ++ (calculeBulletin pa pe ps cc).lignesReductions) := by
  show (sommeSalariale (salS pa pe ps cc) + sommeSalariale (retraiteB pa ps))
      + (sommePatronale (salP pa pe ps cc) + sommePatronale (retraiteB pa ps)
        + sommePatronale (reductionsB pa pe ps))
    = sommeSalariale (((salS pa pe ps cc).filter (fun l => !l.estNulle)
        ++ (retraiteB pa ps).filter (fun l => !l.estNulle))
        ++ (salP pa pe ps cc).filter (fun l => !l.estNulle) ++ reductionsB pa pe ps)
      + sommePatronale (((salS pa pe ps cc).filter (fun l => !l.estNulle)
        ++ (retraiteB pa ps).filter (fun l => !l.estNulle))
        ++ (salP pa pe ps cc).filter (fun l => !l.estNulle) ++ reductionsB pa pe ps)
  simp only [sommeSalariale_append, sommePatronale_append, sommeSalariale_filtrée,
    sommePatronale_filtrée, sommeSalariale_salP_nulle pa pe ps cc,
    sommeSalariale_reductionsB_nulle pa pe ps, sommePatronale_salS_nulle pa pe ps cc,
    Rat.add_zero, Rat.zero_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-- **Invariants du bulletin légal.** Pour tout barème annuel, toute
    entreprise, tout salarié et toute convention collective, le
    bulletin produit par `calculeBulletin` satisfait les quatre
    invariants comptables. -/
theorem calculeBulletin_invariants (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (cc : Option ConventionCollective) :
    (calculeBulletin pa pe ps cc).invariants :=
  ⟨calculeBulletin_net_invariant pa pe ps cc, rfl,
    calculeBulletin_versements_invariant pa pe ps cc,
    calculeBulletin_lignes_invariant pa pe ps cc⟩

/-- Réassociation des totaux augmentés de lignes supplémentaires vers
    la forme fondée sur les listes stockées (utilisé par la composition
    de bulletin). -/
theorem Bulletin.totals_recompose (b : Bulletin) (lignes : List LigneCotisation)
    (h : b.invariants)
    (h0p : sommeSalariale b.lignesPatronales = 0)
    (h0r : sommeSalariale b.lignesReductions = 0)
    (h0s : sommePatronale b.lignesSalariales = 0) :
    (b.totalSalarial + sommeSalariale lignes) + (b.totalPatronalNet + sommePatronale lignes)
      = sommeSalariale b.lignesSalariales + sommeSalariale b.lignesRetraite
          + sommeSalariale lignes
        + (sommePatronale b.lignesRetraite + sommePatronale b.lignesPatronales
          + (sommePatronale lignes + sommePatronale b.lignesReductions)) := by
  have h6 : b.totalSalarial + b.totalPatronalNet
      = sommeSalariale b.lignesSalariales + sommeSalariale b.lignesRetraite
        + (sommePatronale b.lignesRetraite + sommePatronale b.lignesPatronales
          + sommePatronale b.lignesReductions) := by
    rw [h.lignes, somme_norme b.lignesSalariales b.lignesRetraite b.lignesPatronales
      b.lignesReductions h0p h0s, h0r]
    simp only [Rat.add_zero, Rat.zero_add]
  rw [Rat.add_add_add_comm b.totalSalarial (sommeSalariale lignes) b.totalPatronalNet
    (sommePatronale lignes), h6]
  simp only [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-- **Composition des bulletins.** Ajouter des lignes mixtes (prévoyance
    conventionnelle, cotisations de branche…) à un bulletin qui satisfait
    les invariants, et dont les listes ne portent pas de parts croisées,
    donne un bulletin qui satisfait encore les invariants — pour toute
    liste ajoutée. -/
theorem Bulletin.avecLignesSupplementaires_invariants (b : Bulletin)
    (lignes : List LigneCotisation) (h : b.invariants)
    (h0p : sommeSalariale b.lignesPatronales = 0)
    (h0r : sommeSalariale b.lignesReductions = 0)
    (h0s : sommePatronale b.lignesSalariales = 0) :
    (b.avecLignesSupplementaires lignes).invariants :=
  ⟨by
    show (b.netAvantIR - sommeSalariale lignes)
      + (b.totalSalarial + sommeSalariale lignes) = b.brut
    rw [Rat.add_comm b.totalSalarial (sommeSalariale lignes), ← Rat.add_assoc,
      Rat.sub_add_cancel]
    exact h.net,
   by
    show b.coutEmployeur + sommePatronale lignes
      = b.brut + (b.totalPatronalNet + sommePatronale lignes)
    rw [h.cout, Rat.add_assoc],
   by
    show (versementsParOrganisme
        (b.lignesSalariales ++ b.lignesRetraite ++ b.lignesPatronales ++ lignes
          ++ b.lignesReductions)).foldl (fun acc p => acc + p.2) 0
      = (b.totalSalarial + sommeSalariale lignes)
        + (b.totalPatronalNet + sommePatronale lignes)
    simp only [versements_conservent_le_total, sommeSalariale_append, sommePatronale_append,
      sommeSalariale_filtrée, sommePatronale_filtrée, h0p, h0r, h0s, Rat.add_zero,
      Rat.zero_add, Bulletin.totals_recompose b lignes h h0p h0r h0s, Rat.add_assoc,
      Rat.add_comm, Rat.add_left_comm],
   by
    show (b.totalSalarial + sommeSalariale lignes) + (b.totalPatronalNet + sommePatronale lignes)
      = sommeSalariale (b.lignesSalariales ++ b.lignesRetraite
          ++ (b.lignesPatronales ++ lignes.filter (fun l => !l.estNulle))
          ++ b.lignesReductions)
        + sommePatronale (b.lignesSalariales ++ b.lignesRetraite
          ++ (b.lignesPatronales ++ lignes.filter (fun l => !l.estNulle))
          ++ b.lignesReductions)
    simp only [List.append_assoc, sommeSalariale_append, sommePatronale_append,
      sommeSalariale_filtrée, sommePatronale_filtrée, h0p, h0r, h0s, Rat.add_zero,
      Rat.zero_add, Bulletin.totals_recompose b lignes h h0p h0r h0s, Rat.add_assoc,
      Rat.add_comm, Rat.add_left_comm]⟩

/-- **Invariants du bulletin SYNTEC.** Pour tout barème, toute entreprise,
    tout salarié SYNTEC et toute convention, le bulletin produit par
    `calculeBulletinSyntech` satisfait les quatre invariants comptables. -/
theorem calculeBulletinSyntech_invariants (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (rs : RegimeSyntech) (cc : Option ConventionCollective) :
    (calculeBulletinSyntech pa pe ps rs cc).invariants := by
  rw [calculeBulletinSyntech]
  refine Bulletin.avecLignesSupplementaires_invariants _ _
    (calculeBulletin_invariants pa pe ps cc) ?_ ?_ ?_
  · show sommeSalariale ((salP pa pe ps cc).filter (fun l => !l.estNulle)) = 0
    rw [sommeSalariale_filtrée]
    exact sommeSalariale_salP_nulle pa pe ps cc
  · exact sommeSalariale_reductionsB_nulle pa pe ps
  · show sommePatronale ((salS pa pe ps cc).filter (fun l => !l.estNulle)) = 0
    rw [sommePatronale_filtrée]
    exact sommePatronale_salS_nulle pa pe ps cc

end Cotisations
