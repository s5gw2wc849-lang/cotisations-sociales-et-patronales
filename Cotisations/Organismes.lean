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
  l.partSalariale == 0 && l.partPatronale == 0

/-- Somme des parts salariales d'une liste de lignes. -/
def sommeSalariale (l : List LigneCotisation) : Eur :=
  l.foldl (fun acc x => acc + x.partSalariale) 0

/-- Somme des parts patronales (réductions négatives comprises). -/
def sommePatronale (l : List LigneCotisation) : Eur :=
  l.foldl (fun acc x => acc + x.partPatronale) 0

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

/-- Agrège les montants versés à chaque organisme (salarial + patronal),
    dans l'ordre d'apparition. -/
def versementsParOrganisme (l : List LigneCotisation) : List (Organisme × Eur) :=
  let ajout (acc : List (Organisme × Eur)) (ligne : LigneCotisation) :
      List (Organisme × Eur) :=
    let montant := ligne.partSalariale + ligne.partPatronale
    match acc.find? (fun p => p.1 == ligne.organisme) with
    | some _ => acc.map (fun p =>
        if p.1 == ligne.organisme then (p.1, p.2 + montant) else p)
    | none => acc ++ [(ligne.organisme, montant)]
  l.foldl ajout []

end Cotisations