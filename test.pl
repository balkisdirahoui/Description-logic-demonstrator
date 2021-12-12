/*
:-[box].
:-[utils].

*/














/***************************************************BOX**********************************************/
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
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).
/***************************************************UTILS**********************************************/
concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).


genere(Nom) :-
		compteur(V),nombre(V,L1),
		concat([105,110,115,116],L1,L2),
		V1 is V+1,
		dynamic(compteur/1),
		retract(compteur(V)),
		dynamic(compteur/1),
		assert(compteur(V1)),nl,nl,nl,
         	name(Nom,L2).
nombre(0,[]).
nombre(X,L1) :-
		R is (X mod 10),
		Q is ((X-R)//10),
		chiffre_car(R,R1),
		char_code(R1,R2),
		nombre(Q,L),
		concat(L,[R2],L1).
chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').

lecture([X|L]):-read(X), X \= fin, !,lecture(L).
lecture([]).

nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)) :- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),X):-!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).
unique([],[]).
unique([A],[A]).
unique([A,B|C],D) :- delete(A,[B|C],E),
unique(E,F),
append(A,F,D).

append(A,B,B) :- member(A,B),!.
append(A,B,[A|B]).


 delete(_,[],[]).
delete(A,[A],[]).
delete(A,[A|B],B).
 delete(A,[B|C],[B|D]) :- delete(A,C,D), !.

/***************************************************TEST**********************************************/
compteur(1).

prog :-
	premiere_etape(Tbox,Abi,Abr),
	deuxieme_etape(Abi,Abi1,Tbox),
	troisieme_etape(Abi1,Abr).


premiere_etape(Tbox,Abi,Abr) :-
	setof((X,Y), equiv(X,Y),Tbox),
	setof(inst(X,Y), inst(X,Y),Abi),
	setof(instR(X,Y,Z), instR(X,Y,Z),Abr).



	
	
	
	
/*****************************************************/
/*Partie 2 : Validation des propositions*/
/*****************************************************/
deuxieme_etape(Abi,Abi1,Tbox) :-
	saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :-
	nl,
	write('Entrez   le   numero   du   type   de   proposition   que   vous   voulez demontrer :'),
	nl,
	write('1 Une instance donnee appartient a un concept donne.'),
	nl,
	write('2 Deux concepts n"ont pas d"elements en commun(ils ont une intersection vide).'),
	nl,
	read(R),
	suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :-
	acquisition_prop_type1(Abi,Abi1,Tbox),!.

suite(2,Abi,Abi1,Tbox) :-
	acquisition_prop_type2(Abi,Abi1,Tbox),!.

suite(R,Abi,Abi1,Tbox) :-
	nl,
	write('Cette reponse est incorrecte.'),nl,
  saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).


acquisition_prop_type1(Abi,Abi1,Tbox) :-
		part_1_acquisition_prop_type1(Abi,Abi1,Tbox).
part_1_acquisition_prop_type1(Abi,Abi1,Tbox)	:-
		nl,
	  write('Entrez le nom de l\'instance sur laquelle vous voulez faire le test:'),
		nl,
		read(I),
		validate_instance(I),
		write('Entrez le nom du concept sur lequel vous voulez effectuer le test:'),
		part_2_acquisition_prop_type1(I,Abi,Abi1,Tbox).
/*part 2 to add in type 1*/
part_2_acquisition_prop_type1(I,Abi,Abi1,Tbox) :-
	nl,
	read(C),
	/*a*/
	recc_replace(C,C_transformed),
	validate_concept(C_transformed),
	/*b*/
	nnf(not(C_transformed),Prop_to_add_in_Abox),
	concat(Abi,[inst(I,Prop_to_add_in_Abox)],Abi1).

acquisition_prop_type2(Abi,Abi1,Tbox) :-
	part_1_acquisition_prop_type2(Abi,Abi1,Tbox).

part_1_acquisition_prop_type2(Abi,Abi1,Tbox) :-
	nl,
	write('Entrez le nom du premier concept:'),
	nl,
	read(C1),
	recc_replace(C1,C1_transformed),
	validate_concept(C1_transformed),
	part_2_acquisition_prop_type2(C1_transformed,Abi,Abi1,Tbox).
part_2_acquisition_prop_type2(C1_transformed,Abi,Abi1,Tbox) :-
	nl,
	write('Entrez le nom du deuxieme concept:'),
	nl,
	read(C2),
	/* a*/
	recc_replace(C2,C2_transformed),
	validate_concept(C2_transformed),
	nnf(and(C1_transformed,C2_transformed),Prop_to_add_in_Abox),
	concat(Abi,[inst(X,Prop_to_add_in_Abox)],Abi1).
/*
 *
 *Verification sur l'instance
 *
 */
validate_instance(I) :- setof(X, iname(X),L), member(I,L).

/*
 *
 *Verification sur les concepts
 *
 */
validate_concept(C) :- concept(C).


/*
 *  Grammaire syntaxique des concepts
 */
concept(C) :- cnamea(C).
concept(not(C)) :- concept(C).
concept(or(C1,C2)) :- concept(C1), concept(C2).
concept(and(C1,C2)) :- concept(C1), concept(C2).
concept(some(R,C)) :- rname(R), concept(C).
concept(all(R,C)) :- rname(R),concept(C).


/*
 * fonction de remplacement reccuressive
	test : sculpteur, editeur
 */

recc_replace(C_origin, C_origin) :- concept(C_origin).
recc_replace(and(C1,C2),C_target) :- recc_replace(C1,C_temp1), recc_replace(C2,C_temp2), recc_replace(and(C_temp1,C_temp2),C_target).
recc_replace(or(C1,C2),C_target) :- recc_replace(C1,C_temp1), recc_replace(C2,C_temp2), recc_replace(or(C_temp1,C_temp2),C_target).
recc_replace(not(C_origin),C_target) :- recc_replace(C_origin,C_temp), recc_replace(not(C_temp),C_target).
recc_replace(some(R,C_origin),C_target) :- recc_replace(C_origin,C_temp), recc_replace(some(R,C_temp),C_target).
recc_replace(some(R,C_origin),C_target) :- recc_replace(C_origin,C_temp), recc_replace(all(R,C_temp),C_target).
recc_replace(C_origin,C_target) :- equiv(C_origin,X), recc_replace(X,C_target).


/*****************************************************/
/*Partie 3 : Tri et resolution */
/*****************************************************/
troisieme_etape(Abi,Abr) :-
	/*simplify_Abox(Abi),*/
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	resolution(Lie,Lpt,Li,Lu,Ls,Abr),
	nl,
	write('Youpiiiiii, on a demontre la proposition initiale!!!').

literal(X) :- cnamea(X).
literal(X) :- not(Y) = X , literal(Y).



/*****************************************************/
/*tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls)*/
/*****************************************************/
/*traitement des litteraux*/
tri_Abox([],[],[],[],[],[]).
tri_Abox([inst(I,C)],Lie,Lpt,Li,Lu,[inst(I,C)|Ls]):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls), literal(C), iname(I).
tri_Abox([inst(I,C)|Abi],Lie,Lpt,Li,Lu,[inst(I,C)|Ls]):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	iname(I),
	literal(C).

/*traitement existe*/
tri_Abox([inst(I,some(R,C))],[inst(I,some(R,C))|Lie],Lpt,Li,Lu,Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),
	iname(I), concept(C), rname(R).
tri_Abox([inst(I,some(R,C))|Abi],[inst(I,some(R,C))|Lie],Lpt,Li,Lu,Ls):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	iname(I), concept(C), rname(R).

/*traitement quelque soit*/
tri_Abox([inst(I,all(R,C))],Lie,[inst(I,all(R,C))|Lpt],Li,Lu,Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),
	iname(I), concept(C), rname(R).
tri_Abox([inst(I,all(R,C))|Abi],Lie,[inst(I,all(R,C))|Lpt],Li,Lu,Ls):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	iname(I), concept(C), rname(R).

/* traitement and*/
tri_Abox([inst(I,and(C1,C2))],Lie,Lpt,[inst(I,and(C1,C2))|Li],Lu,Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),iname(I), concept(C1), concept(C2).
tri_Abox([inst(I,and(C1,C2))|Abi],Lie,Lpt,[inst(I,and(C1,C2))|Li],Lu,Ls):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),iname(I), concept(C1), concept(C2).

/*traitement or*/
tri_Abox([inst(I,or(C1,C2))],Lie,Lpt,Li,[inst(I,or(C1,C2))|Lu],Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),iname(I), concept(C1), concept(C2).
tri_Abox([inst(I,or(C1,C2))|Abi],Lie,Lpt,Li,[inst(I,or(C1,C2))|Lu],Ls):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),iname(I), concept(C1), concept(C2).




/*****************************************************/
/*resolution(Lie,Lpt,Li,Lu,Ls,Abr)*/
/*****************************************************/

resolution([],[],[],[],Ls,[]) :- testclash(Ls).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
	testclash(Ls),
	Lie \== [],
	complete_some(Lie,Lpt,Li,Lu,Ls,Abr).
	

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
	testclash(Ls),
	Li \== [],
	transformation_and(Lie,Lpt,Li,Lu,Ls,Abr).
	


resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
	testclash(Ls),
	Lpt \==[],
	deduction_all(Lie,Lpt,Li,Lu,Ls,Abr).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
	testclash(Ls),
	Lu \==[],
	transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).

/*****************************************************/
/* Test clash */
/*****************************************************/
%exemple jeu de test (voir plus dans rapport ): testclash([inst(david,not(personne)),inst(david,personne)])
testclash([]).
testclash([inst(I,C1)|Ls]) :-
	nnf(not(C1),Z), 
    \+ memberchk(inst(I,Z),Ls),
    testclash(Ls).


/*****************************************************/
/* complete_some([],Lpt,Li,Lu,Ls,Abr)*/
/*****************************************************/
/*test david, all(aEcrit,livre)*/

complete_some([],Lpt,Li,Lu,Ls,Abr).
complete_some([inst(I,some(R,C))],Lpt,Li,Lu,Ls,Abr) :-
	
	nl,
	write("**************************************************************************************************"),nl,
	write("          Evolution de la Abox pour la propostion :"),affiche_instance(inst(I,some(R,C))),nl,
	write("**************************************************************************************************"),	
	nl,	
	genere(B),
	concat([instR(I,B,R)],Abr,Abr1),
	concept(C), rname(R), iname(I), genere(B),
	evolue(inst(B,C),[],Lpt,Li,Lu,Ls,[],Lpt1,Li1,Lu1,Ls1),
	affiche_evolution_Abox(Ls,Lie,Lpt,Li,Lu,Abr,Ls1,Lie1,Lpt,Li1,Lu1,Abr1),!,
	resolution(Lie1, Lpt1,Li1,Lu1,Ls1,Abr1).

complete_some([inst(I,some(R,C))|Lie],Lpt,Li,Lu,Ls,Abr) :-
	nl,
	write("**************************************************************************************************"),nl,
	write("          Evolution de la Abox pour la propostion :"),affiche_instance(inst(I,some(R,C))),nl,
	write("**************************************************************************************************"),	
	nl,
	concept(C), rname(R), iname(I), genere(B),
	genere(B),
	concat([instR(I,B,R)],Abr,Abr1),
	evolue(inst(B,C),Lie,Lpt,Li,Lu,Ls,Lie,Lpt1,Li1,Lu1,Ls1),
	affiche_evolution_Abox(Ls,Lie,Lpt,Li,Lu,Abr,Ls1,Lie1,Lpt,Li1,Lu1,Abr1),!,
	resolution(Lie1, Lpt1,Li1,Lu1,Ls1,Abr1).

/*****************************************************/
/* deduction_all(Lie,[],Li,Lu,Ls,Abr)*/
/*****************************************************/

/*test michelAnge, some(aCree,sculpture)*/
deduction_all(Lie,[],Li,Lu,Ls,Abr).

deduction_all(Lie,[inst(I,all(R,C))],Li,Lu,Ls,Abr) :-
    nl,
	write("**************************************************************************************************"),nl,
	write("          Evolution de la Abox pour la propostion :"),affiche_instance(inst(I,all(R,C))),nl,
	write("**************************************************************************************************"),	
	nl,	
	member(instR(I,B,R), Abr),
	iname(I),iname(B),concept(C),rname(R),
	evolue(inst(B,C),Lie,[],Li,Lu,Ls,Lie1,[],Li1,Lu1,Ls1),
	affiche_evolution_Abox(Ls,Lie,[],Li,Lu,Abr,Ls1,Lie1,[],Li1,Lu1,Abr),!,
	resolution(Lie1, Lpt1,Li1,Lu1,Ls1,Abr).

deduction_all(Lie,[inst(I,all(R,C))|Lpt],Li,Lu,Ls,Abr) :-
	nl,
	write("**************************************************************************************************"),nl,
	write("          Evolution de la Abox pour la propostion :"),affiche_instance(inst(I,all(R,C))),nl,
	write("**************************************************************************************************"),	
	nl,	
	member(instR(I,B,R), Abr),
	iname(I),iname(B),concept(C),rname(R),
	evolue(inst(B,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt,Li1,Lu1,Ls1),
	affiche_evolution_Abox(Ls,Lie,Lpt,Li,Lu,Abr,Ls1,Lie1,Lpt,Li1,Lu1,Abr),!,
	resolution(Lie1, Lpt1,Li1,Lu1,Ls1,Abr).
/*ajoute a la abox la formule (b,c) et retire le premier element de la liste Lpt*/

/*****************************************************/
/* transformation_and(Lie,Lpt,[inst(I,and(C1,C2))|Li],Lu,Ls,Abr)*/
/*****************************************************/
%test : (david,or(personne,sculpture)) , (vinci,or(personne,objet))
transformation_and(Lie,Lpt,[inst(I,and(C1,C2))|Li],Lu,Ls,Abr)  :-
    nl,
	write("**************************************************************************************************"),nl,
	write("          Evolution de la Abox pour la propostion :"),affiche_instance(inst(I,and(C1,C2))),nl,
	write("**************************************************************************************************"),	
	nl,	
	evolue(inst(I,C1),Lie,Lpt,[],Lu,Ls,Lie1,Lpt1,[],Lu1,Ls1),
	evolue(inst(I,C2),Lie,Lpt,[],Lu,Ls1,Lie1,Lpt1,[],Lu1,Ls2),
	affiche_evolution_Abox(Ls,Lie,Lpt,Li,Lu,Abr,Ls2,Lie1,Lpt1,Li1,Lu1,Abr),!,
	resolution(Lie1, Lpt1,Li1,Lu1,Ls2,[]).
/*ajoute a la abox les instances (I,C1) et (I,C2) retire le premier element de la liste Li*/



/*****************************************************/
/* transformation_or(Lie,Lpt,Li,[inst(I,or(C1,C2))|Lu],Ls,Abr)*/
/*****************************************************/
%test (david,and(personne,sculpture))

transformation_or(Lie,Lpt,Li,[inst(I,or(C1,C2))|Lu],Ls,Abr) :-
	nl,
	write("***********************************************************************"),nl,
	write("          Evolution de la Abox pour la propostion :"),affiche_instance(inst(I,or(C1,C2))),nl,
	write("***********************************************************************"),	nl,nl,	
	
	evolue(inst(I,C1),Lie,Lpt,Li,[],Ls,Lie1,Lpt1,Li1,[],Ls1),
	write("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++"),nl,
	write("                       Branche 1                           "), nl,
	write("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++"),	nl,nl,
	affiche_evolution_Abox(Ls,Lie,Lpt,Li,Lu,Abr,Ls1,Lie1,Lpt1,Li1,Lu1,Abr),!,
	resolution(Lie1, Lpt1,Li1,Lu1,Ls1,[]) ,
	
	evolue(inst(I,C2),Lie,Lpt,Li,[],Ls,Lie1,Lpt1,Li1,[],Ls2),
	write("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++"),nl,
	write("                        Branche 2                           "), nl,
	write("+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++"),	nl,nl,
	affiche_evolution_Abox(Ls,Lie,Lpt,Li,Lu,Abr,Ls2,Lie1,Lpt1,Li1,Lu1,Abr),!,
	resolution(Lie1, Lpt1,Li1,Lu1,Ls2,[]).


/*****************************************************/
/* EVOLUTION*/
/*****************************************************/
/*evolution d'un literal*/
evolue(inst(B,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1) :-
	literal(C),
	Lie = Lie1,
	Lpt = Lpt1,
	Li = Li1,
	Lu = Lu1,
	concat([inst(B,C)],Ls,Z),
	unique(Z,Ls1)
	.

/*evolution d'un or*/
evolue(inst(B,or(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1) :-
	concept(C1),concept(C2),
	Lie = Lie1,
	Lpt = Lpt1,
	Li = Li1,
	Ls = Ls1,
	concat([inst(B,or(C1,C2))],Lu,Z),
	unique(Z,Lu1)
	.
/*evolution d'un and*/
evolue(inst(B,and(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1) :-
	concept(C1),concept(C2),
	Lie = Lie1,
	Lpt = Lpt1,
	Lu = Lu1,
	Ls = Ls1,
	concat([inst(B,and(C1,C2))],Li,Z),
	unique(Z,Li1)
	.
/*evolution d'un all*/
evolue(inst(B,all(R,C)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1) :-
	concept(C),
	Lie = Lie1,
	Lu = Lu1,
	Li = Li1,
	Ls = Ls1,
	concat([inst(B,all(R,C))],Lpt,Z),
	unique(Z,Lpt1)
	.


/*evolution d'un some*/
evolue(inst(B,some(R,C)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1) :-
	concept(C),
	Lu = Lu1,
	Lpt = Lpt1,
	Li = Li1,
	Ls = Ls1,
	concat([inst(B,some(R,C))],Lie,Z),
	unique(Z,Lie1)
	.


/*****************************************************/
/* AFFICHAGE*/
/*****************************************************/
affiche_role(instR(A,B,R)):- write(A), tab(1) , write(R), tab(1) , write(B).

affiche_literal(not(C)):- write("¬("), write(C),write(")"),!.
affiche_literal(C):- write(C),!.

affiche_concept(C) :- literal(C), affiche_literal(C),!.
affiche_concept(C) :- cnamena(C), affiche_literal(C),!.
affiche_concept(or(C1,C2)) :- write("("),affiche_concept(C1), write(" ⊔ ") , affiche_concept(C2), write(")"),!.
affiche_concept(and(C1,C2)) :- write("("),affiche_concept(C1), write(" ⊓ ") , affiche_concept(C2), write(")"),!.
affiche_concept(some(R,C)) :- write("("), write("∃"),write(R) , write("."),affiche_concept(C),write(")"),!.
affiche_concept(all(R,C)) :- write("("),write("∀"), write(R) , write("."),affiche_concept(C),write(")"),!.

affiche_instance(inst(B,C)) :- write(B), write(":"), affiche_concept(C),!.

affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
	write("contenu de Ls avant l'application de la regle:"),nl,
	write("Ls = "),
	write("["),
	nl
	,
	affiche_liste_inst(Ls1),
	write("]"),
	nl,
	write("contenu de Ls apres l'application de la regle:"),nl,
	write("Ls_Up = "),
	write("["),
	nl
	,
	nl
	,
	affiche_liste_inst(Ls2),
	write("]"),
	nl,
	write("contenu de Lie avant l'application de la regle:"),nl,
	write("Lie = "),
	write("["),
	nl
	,
	affiche_liste_inst(Lie1),
	write("]"),
	nl,
	write("contenu de Lie apres l'application de la regle:"),nl,
	write("Lie_Up = "),
	write("["),
	nl
	,

	affiche_liste_inst(Lie2),
	write("]"),
	nl,
	
	nl
	,
	write("contenu de Lpt avant l'application de la regle:"),nl,
	write("Lpt = "),
	write("["),
	nl
	,
	affiche_liste_inst(Lpt1),
	write("]"),
	nl,
	write("contenu de Lpt apres l'application de la regle:"),nl,
	write("Lpt_Up = "),
	write("["),
	nl
	,
	affiche_liste_inst(Lpt2),
	write("]"),
	nl,
	
	nl
	,
	write("contenu de Li avant l'application de la regle:"),nl,
	write("Li = "),
	write("["),
	nl
	,
	affiche_liste_inst(Li1),
	write("]"),
	nl,
	write("contenu de Li apres l'application de la regle:"),nl,
	write("Li_Up = "),
	write("["),
	nl
	,
	affiche_liste_inst(Li2),
	write("]"),
	nl,
	
	nl
	,
	write("contenu de Lu avant l'application de la regle:"),nl,
	write("Lu = "),
	write("["),
	nl
	,
	affiche_liste_inst(Lu1),
	write("]"),
	nl,
	write("contenu de Lu apres l'application de la regle:"),nl,
	write("Lu_Up = "),
	write("["),
	nl
	,

	affiche_liste_inst(Lu2),
	write("]"),
	nl,
	
	nl
	,
	write("contenu de Abr avant l'application de la regle:"),nl,
	write("Abr = "),
	write("["),
	nl
	,
	affiche_liste_role(Abr1),
	write("]"),
	nl,
	write("contenu de Abr apres l'application de la regle:"),nl,
	write("Abr_Up = "),
	write("["),
	nl
	,
	affiche_liste_role(Abr2),
	write("]"),
	nl.
affiche_liste_inst([]).
affiche_liste_inst([X|L]) :- affiche_instance(X), write(","), nl, affiche_liste_inst(L).

affiche_liste_role([]).
affiche_liste_role([X|L]) :- affiche_role(X), write(","),nl, affiche_liste_role(L).
