/-
Protection sociale complémentaire issue de la convention collective :
mutuelle (santé), prévoyance, retraite supplémentaire, caisse de congés
payés conventionnelle.

La convention collective est intégrée ici comme unique source de
cotisations complémentaires : le projet code les règles légales et
s'interfacera avec la convention applicable à l'entreprise (une seule
convention par salarié). Les lignes salariales et patronales de chaque
garantie (mutuelle, retraite supplémentaire) partagent la même
mécanique via des helpers paramétrés par la cote.

Contraintes légales vérifiables :
- part patronale de mutuelle ≥ 50 % du coût total (art. L911-7 CSS) ;
- prévoyance décès des cadres : cotisation ≥ 1,5 % de la tranche 1,
  prise en charge patronale ≥ 60 % (art. L911-2 CSS).
-/
import Cotisations.Assiette
import Cotisations.Organismes
import Cotisations.Parametres

namespace Cotisations

/-- La part patronale de mutuelle couvre-t-elle au moins 50 % du coût ? -/
def mutuelleConforme (partPatronale mutuelleTotale : Eur) : Bool :=
  mutuelleTotale ≤ 2 * partPatronale

/-- La prévoyance cadres respecte-t-elle le minimum légal (1,5 % de la
    tranche 1, ≥ 60 % à la charge de l'employeur) ? -/
def prevoyanceCadresConforme (taux partPatronale : Rat) : Bool :=
  taux ≥ 0.015 && partPatronale ≥ 0.60

/-- Ligne de mutuelle (salariale ou patronale) : assiette = coût total,
    montant = la part correspondante ; émise si la part est non nulle. -/
def lignesMutuelle (cc : ConventionCollective) (salariale : Bool) : List LigneCotisation :=
  let montant := if salariale then cc.mutuelleSalariale else cc.mutuellePatronale
  if montant > 0 then
    [ ligneTauxUnique
        (if salariale then "Complémentaire santé (mutuelle) — part salariale"
         else "Complémentaire santé (mutuelle) — part patronale")
        .mutuelle .cotisation salariale (cc.mutuelleSalariale + cc.mutuellePatronale) montant ]
  else []

/-- Ligne de retraite supplémentaire conventionnelle (une cote, une
    tranche) : émise si le taux correspondant est non nul. -/
def lignesRetraiteSupp (rc : RegimeComplementaire) (nom : String) (salariale : Bool)
    (assiette : Eur) : List LigneCotisation :=
  let taux := if salariale then rc.tauxSalarial else rc.tauxPatronal
  if taux > 0 then
    [ligneTauxUnique nom .retraiteSupplementaire .cotisation salariale assiette (taux * assiette)]
  else []

/-- Lignes salariales issues de la convention collective. -/
def lignesConventionSalariales (cc : ConventionCollective) (t : Tranches) :
    List LigneCotisation :=
  lignesMutuelle cc true
  ++ (if cc.prevoyanceTauxT1 > 0 then
    [ ligneTauxUnique "Prévoyance — part salariale" .prevoyance .cotisation true t.tranche1
        ((1 - cc.prevoyancePartPatronale) * cc.prevoyanceTauxT1 * t.tranche1) ]
    else [])
  ++ lignesRetraiteSupp cc.retraiteSupplementaireT1
       "Retraite supplémentaire — T1, part salariale" true t.tranche1
  ++ lignesRetraiteSupp cc.retraiteSupplementaireT2
       "Retraite supplémentaire — T2, part salariale" true t.tranche2

/-- Lignes patronales issues de la convention collective. -/
def lignesConventionPatronales (cc : ConventionCollective) (t : Tranches) :
    List LigneCotisation :=
  lignesMutuelle cc false
  ++ (if cc.prevoyanceTauxT1 > 0 then
    [ ligneTauxUnique "Prévoyance — part patronale" .prevoyance .cotisation false t.tranche1
        (cc.prevoyancePartPatronale * cc.prevoyanceTauxT1 * t.tranche1) ]
    else [])
  ++ lignesRetraiteSupp cc.retraiteSupplementaireT1
       "Retraite supplémentaire — T1, part patronale" false t.tranche1
  ++ lignesRetraiteSupp cc.retraiteSupplementaireT2
       "Retraite supplémentaire — T2, part patronale" false t.tranche2
  ++ (if cc.tauxCaisseCongesPayes > 0 then
    let a := t.tranche1 + t.tranche2 + t.tranche3
    [ ligneTauxUnique "Caisse de congés payés / intempéries (conventionnelle)"
        .caisseCongesPayes .cotisation false a (cc.tauxCaisseCongesPayes * a) ]
    else [])

end Cotisations
