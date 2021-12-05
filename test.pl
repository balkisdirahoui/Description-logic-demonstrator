:-[box].
:-[utils].
compteur(1).

prog :-
	premiere_etape(Tbox,Abi,Abr),
	deuxieme_etape(Abi,Abi1,Tbox),
	troisieme_etape(Abi1,Abr).

premiere_etape(Tbox,Abi,Abr) :- setof((X,Y), equiv(X,Y),Tbox),setof((X,Y), inst(X,Y),Abi),setof((X,Y,Z), instR(X,Y,Z),Abr).

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
	write(C_transformed),
	validate_concept(C_transformed),
	nnf(not(inst(I,C_transformed)),Prop_to_add_in_Abox),
	concat(Abi,[Prop_to_add_in_Abox],Abi1),
	write(Abi1).

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
part_2_acquisition_prop_type2(C1,Abi,Abi1,Tbox) :-
	nl,
	write('Entrez le nom du deuxieme concept:'),
	nl,
	read(C2),
	recc_replace(C2,C2_transformed),
	validate_concept(C2_transformed),
	nnf(some(X,and(C1,C2)),Prop_to_add_in_Abox),
	concat(Abi,[Prop_to_add_in_Abox],Abi1),
	write(Abi1).
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
 */
recc_replace(C_origin, C_origin) :- concept(C_origin).
recc_replace(and(C1,C2),C_target) :- recc_replace(C1,C_temp1), recc_replace(C2,C_temp2), recc_replace(and(C_temp1,C_temp2),C_target).
recc_replace(or(C1,C2),C_target) :- recc_replace(C1,C_temp1), recc_replace(C2,C_temp2), recc_replace(or(C_temp1,C_temp2),C_target).
recc_replace(not(C_origin),C_target) :- recc_replace(C_origin,C_temp), recc_replace(not(C_temp),C_target).
recc_replace(some(R,C_origin),C_target) :- recc_replace(C_origin,C_temp), recc_replace(some(R,C_temp),C_target).
recc_replace(some(R,C_origin),C_target) :- recc_replace(C_origin,C_temp), recc_replace(all(R,C_temp),C_target).
recc_replace(C_origin,C_target) :- equiv(C_origin,X), recc_replace(X,C_target).

literal(X) :- cnamea(X).
literal(X) :- not(Y) = X , literal(Y).

troisieme_etape(Abi,Abr) :-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	resolution(Lie,Lpt,Li,Lu,Ls,Abr),
	nl,
	write('Youpiiiiii, on a demontre la proposition initiale !!!').

tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls):-
	setof((Ie,some(Re,Ce)), member((Ie,some(Re,Ce),Abi)),Lie),iname(Ie), concept(Ce), rname(Re),
	setof((Ipt,some(Rpt,Cpt)), member((Ipt,all(Rpt,Cpt),Abi)),Lpt),iname(Ipt), concept(Cpt), rname(Rpt),
	setof((Ii,and(Ci1,Ci2))), member((Ii,and(Ci1,Ci2),Abi)),Li),iname(Ii), concept(Ci1), concept(Ci2),
	setof((Iu,and(Cu1,Cu2))), member((Iu,and(Cu1,Cu2),Abi)),Li),iname(Iu), concept(Cu1), concept(Cu2),
	setof((Is,Cs),member((Is,Cs),Abi),Ls), iname(Is), literal(Cs).


resolution(Abi,Lie,Lpt,Li,Lu,Ls) :-
	complete_some(Lie,Lpt,Li,Lu,Ls,Abr),
	transformation_and(Lie,Lpt,Li,Lu,Ls,Abr),
	deduction_all(Lie,Lpt,Li,Lu,Ls,Abr),
	transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).

complete_some(Lie,Lpt,Li,Lu,Ls,Abr) :-
	/*to complete*/
transformation_and(Lie,Lpt,Li,Lu,Ls,Abr) :-
	/*to complete*/
deduction_all(Lie,Lpt,Li,Lu,Ls,Abr) :-
	/*to complete*/
transformation_or(Lie,Lpt,Li,Lu,Ls,Abr) :-
	/*to complete*/
evolue(A, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :-
	/*to complete*/
test_clash(Abi) :-
	/*to complete*/
affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
	/*to complete*/
