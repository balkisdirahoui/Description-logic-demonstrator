equiv(sculpteur,and(personne,some(aCree,sculpture))).
equiv(auteur,and(personne,some(aEcrit,livre))).
equiv(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))).
equiv(parent,and(personne,some(aEnfant,anything))).

cnamea(personne).
cnamea(livre).
cnamea(objet).
cnamea(sculpture).
cnamea(anything).
cnamea(nothing).
cnamena(auteur).
cnamena(editeur).
cnamena(sculpteur).
cnamena(parent).
iname(michelAnge).
iname(david).
iname(sonnets).
iname(vinci).
iname(joconde).
rname(aCree).
rname(aEcrit).
rname(aEdite).
rname(aEnfant).
inst(michelAnge,personne).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).
inst(vinci, sculpteur).
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).
