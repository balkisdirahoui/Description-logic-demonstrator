:-[box].
:-[utils].
compteur(1).

prog :-
	premiere_etape(Tbox,Abi,Abr),
	deuxieme_etape(Abi,Abi1,Tbox),
	troisieme_etape(Abi1,Abr).

premiere_etape(Tbox,Abi,Abr) :-
	setof((X,Y), equiv(X,Y),Tbox),
	setof(inst(X,Y), inst(X,Y),Abi),
	setof((X,Y,Z), instR(X,Y,Z),Abr).

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
part_2_acquisition_prop_type1(I,Abi,Abi1,Tbox) :-
	nl,
	read(C),
	recc_replace(C,C_transformed),
	validate_concept(C_transformed),
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


troisieme_etape(Abi,Abr) :-
	/*simplify_Abox(Abi),*/
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	resolution(Lie,Lpt,Li,Lu,Ls,Abr),
	nl,
	write('Youpiiiiii, on a demontre la proposition initiale !!!').

literal(X) :- cnamea(X).
literal(X) :- not(Y) = X , literal(Y).


/*traitement des litteraux*/
tri_Abox([],[],[],[],[],[]).
tri_Abox([inst(I,C)],Lie,Lpt,Li,Lu,[(I,C)|Ls]):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls), literal(C), iname(I).
tri_Abox([inst(I,C)|Abi],Lie,Lpt,Li,Lu,[(I,C)|Ls]):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	iname(I),
	literal(C).
/*traitement existe*/
tri_Abox([inst(I,some(R,C))],[(I,some(R,C))|Lie],Lpt,Li,Lu,Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),
	iname(I), concept(C), rname(R).
tri_Abox([inst(I,some(R,C))|Abi],[(I,some(R,C))|Lie],Lpt,Li,Lu,Ls):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	iname(I), concept(C), rname(R).

/*traitement quelque soit*/
tri_Abox([inst(I,all(R,C))],Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),
	iname(I), concept(C), rname(R).
tri_Abox([inst(I,all(R,C))|Abi],Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	iname(I), concept(C), rname(R).

/* traitement and*/
tri_Abox([inst(I,and(C1,C2))],Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),iname(I), concept(C1), concept(C2).
tri_Abox([inst(I,and(C1,C2))|Abi],Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),iname(I), concept(C1), concept(C2).

/*traitement or*/
tri_Abox([inst(I,or(C1,C2))],Lie,Lpt,Li,[(I,or(C1,C2))|Lu],Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),iname(I), concept(C1), concept(C2).
tri_Abox([inst(I,or(C1,C2))|Abi],Lie,Lpt,Li,[inst(I,or(C1,C2))|Lu],Ls):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),iname(I), concept(C1), concept(C2).


resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
	/*test_clash()*/
	Lie \== [],
	complete_some(Lie,Lpt,Li,Lu,Ls,Abr).
	/*evolution
	affiche_evolution
	resolution
	*/

/*resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
	test_clash()
	transforamtion_and(Lie,Lpt,Li,Lu,Ls,Abr),
	evolution
	affiche_evolution
	resolution
	*/

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
	/*test_clash()*/
	Lpt \==[],
	deduction_all(Lie,Lpt,Li,Lu,Ls,Abr).
	/*evolution
	affiche_evolution
	resolution
	*/

/*resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
	test_clash()
	transforamtion_or(Lie,Lpt,Li,Lu,Ls,Abr),
	evolution ( va se charger de supprimer le preùier element de chaque liste)
	affiche_evolution
	resolution
	*/

/*test david, all(aEcrit,livre)*/
complete_some([],Lpt,Li,Lu,Ls,Abr).

complete_some([(I,some(R,C))],Lpt,Li,Lu,Ls,Abr) :-
	complete_some([],Lpt,Li,Lu,Ls_after,Abr_after),
	concept(C), rname(R), iname(I), genere(B),
	concat([instR(I,B,R)],Abr,Abr_after),
	concat([(B,C)],Ls,Ls_after).

complete_some([(I,some(R,C))|Lie],Lpt,Li,Lu,Ls,Abr) :-
	complete_some(Lie,Lpt,Li,Lu,Ls_after,Abr_after),
	concept(C), rname(R), iname(I), genere(B),
	concat([instR(I,B,R)],Abr,Abr_after),
	concat([(B,C)],Ls,Ls_after).

/*test michelAnge, some(aCree,sculpture)*/
deduction_all(Lie,[],Li,Lu,Ls,Abr).

deduction_all(Lie,[(I,all(R,C))],Li,Lu,Ls,Abr) :-
	member(instR(I,B,R), Abr), iname(I),iname(B),concept(C),rname(R),
	deduction_all(Lie,[],Li,Lu,Ls_after,Abr_after),
	enleve(instR(I,B,R), Abr,Abr_after),
	concat([(B,C)],Ls,Ls_after).

deduction_all(Lie,[(I,all(R,C))|Lpt],Li,Lu,Ls,Abr) :-
	member((I,B,R), Abr), iname(I),iname(B),concept(C),rname(R),
	deduction_all(Lie,Lpt,Li,Lu,Ls_after,Abr_after),
	enleve((I,B,R), Abr,Abr_after),
	concat([(B,C)],Ls,Ls_after).


evolue((2,B,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1) :-
