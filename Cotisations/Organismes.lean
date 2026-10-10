/-
Organismes collecteurs et typologie des lignes de bulletin.

Chaque cotisation, contribution ou taxe est rattachée à l'organisme qui
la recouvre, à sa nature juridique et à sa voie de déclaration (DSN).
-/
import Cotisations.Basic

namespace Cotisations

/-- Organismes destinataires des cotisations et contributions. -/
inductive Organisme where
  | urssaf                -- Urssaf / CNAV / CNAF / branche famille et chômage (CTP)
  | agircArrco            -- Institutions de retraite complémentaire Agirc-Arrco
  | apec                  -- APEC (cadres)
  | dgfip                 -- DGFiP (taxe sur les salaires)
  | carsat                -- Carsat / Cramif (accidents du travail et maladies professionnelles)
  | mutuelle              -- Organisme complémentaire santé (mutuelle, institution, fondation)
  | prevoyance            -- Organisme de prévoyance
  | retraiteSupplementaire -- PER collectif / retraite supplémentaire conventionnelle
  | caisseCongesPayes     -- Caisses de congés payés (BTP, transport, spectacle…)
  deriving Repr, DecidableEq, Inhabited

/-- Nature juridique du prélèvement. -/
inductive NatureCotisation where
  | cotisation    -- cotisation de sécurité sociale ou de retraite
  | contribution  -- contribution (CSG, CRDS, CSA, FNAL, forfait social…)
  | taxe          -- taxe (apprentissage, salaires, versement mobilité…)
  | remboursement -- exonération partielle remboursée (exonération zones…)
  | reduction     -- réduction / déduction (RGDU, déduction forfaitaire heures sup…)
  deriving Repr, DecidableEq, Inhabited

/-- Partie du bulletin concernée. -/
inductive Cote where
  | salariale | patronale | mixte
  deriving Repr, DecidableEq, Inhabited

/-- Une ligne de cotisation du bulletin (après la ligne « brut »).

    `partSalariale` et `partPatronale` sont positifs pour un prélèvement,
    négatifs pour une réduction. Pour la réduction générale (RGDU), les
    champs `imputationUrssaf` et `imputationIRC` donnent le détail de
    l'imputation entre les deux organismes (utile en DSN). -/
structure LigneCotisation where
  nom : String
  organisme : Organisme
  nature : NatureCotisation
  cote : Cote
  assiette : Eur
  partSalariale : Eur := 0
  partPatronale : Eur := 0
  imputationUrssaf : Eur := 0
  imputationIRC : Eur := 0
  commentaire : String := ""
  deriving Repr, DecidableEq, Inhabited

def LigneCotisation.estNulle (l : LigneCotisation) : Bool :=
  decide (l.partSalariale = 0 ∧ l.partPatronale = 0)

/-- Une ligne nulle porte deux parts nulles. -/
theorem LigneCotisation.estNulle_parts (l : LigneCotisation) (h : l.estNulle = true) :
    l.partSalariale = 0 ∧ l.partPatronale = 0 :=
  of_decide_eq_true h

/-- Somme générique d'une quantité `f` sur une liste de lignes. -/
def sommeSur (f : LigneCotisation → Eur) (l : List LigneCotisation) : Eur :=
  l.foldl (fun acc x => acc + f x) 0

/-- Somme des parts salariales d'une liste de lignes. -/
def sommeSalariale (l : List LigneCotisation) : Eur :=
  sommeSur (fun x => x.partSalariale) l

/-- Somme des parts patronales (réductions négatives comprises). -/
def sommePatronale (l : List LigneCotisation) : Eur :=
  sommeSur (fun x => x.partPatronale) l

/-! ### Constructeurs de lignes -/

/-- Ligne de cotisation à part unique : `salariale = true` place le
    montant en part salariale, sinon en part patronale. -/
def ligneTauxUnique (nom : String) (org : Organisme) (nat : NatureCotisation)
    (salariale : Bool) (assiette montant : Eur) (commentaire : String := "") :
    LigneCotisation :=
  { nom := nom, organisme := org, nature := nat
    cote := if salariale then .salariale else .patronale
    assiette := assiette
    partSalariale := if salariale then montant else 0
    partPatronale := if salariale then 0 else montant
    commentaire := commentaire }

/-- Ligne de cotisation mixte (parts salariale et patronale sur une même
    ligne, comme la retraite complémentaire ou la prévoyance). -/
def ligneMixte (nom : String) (org : Organisme) (nat : NatureCotisation)
    (assiette partSalariale partPatronale : Eur) (commentaire : String := "") :
    LigneCotisation :=
  { nom := nom, organisme := org, nature := nat, cote := .mixte
    assiette := assiette
    partSalariale := partSalariale, partPatronale := partPatronale
    commentaire := commentaire }

/-- Liste exhaustive des organismes collecteurs (sans doublon). -/
def Organisme.tous : List Organisme :=
  [.urssaf, .agircArrco, .apec, .dgfip, .carsat, .mutuelle, .prevoyance,
   .retraiteSupplementaire, .caisseCongesPayes]

theorem Organisme.tous_complet (o : Organisme) : o ∈ Organisme.tous := by
  cases o <;> simp [Organisme.tous]

/-- Montant total (salarial + patronal) versé à un organisme donné. -/
def montantOrganisme (org : Organisme) (l : List LigneCotisation) : Eur :=
  l.foldl (fun acc x =>
    acc + (if x.organisme == org then x.partSalariale + x.partPatronale else 0)) 0

/-- Ventilation des versements par organisme : chaque organisme de la
    liste exhaustive reçoit le total de ses lignes (montant nul compris). -/
def versementsParOrganisme (l : List LigneCotisation) : List (Organisme × Eur) :=
  Organisme.tous.map (fun org => (org, montantOrganisme org l))

end Cotisations