:-[box].
:-[utils].
compteur(1).

prog :-
	premiere_etape(Tbox,Abi,Abr),
	deuxieme_etape(Abi,Abi1,Tbox),
	troisieme_etape(Abi1,Abr).

premiere_etape(Tbox,Abi,Abr) :- setof((X,Y), equiv(X,Y),Tbox),setof((X,Y), inst(X,Y),Abi),setof((X,Y,Z), instR(X,Y,Z),Abr).
%(auteur, and(personne, some(aEcrit, livre)))
%autoref((C,D),Tbox) :- write(C),nl,write(D).

autoref((C,all(R,C2)),Tbox) :- write(C),nl,write(R)
,nl,write(C2),[(C2,some(R,C3))|Tbox], +\ C2 ==C3,!,autoref((C,all(R,C2)),Tbox) .
%autoref((C,D),[]). 
	
	
	
	
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





part_2_acquisition_prop_type2(C1,Abi,Abi1,Tbox) :-
	nl,
	write('Entrez le nom du deuxieme concept:'),
	nl,
	read(C2),
	/* a*/
	recc_replace(C2,C2_transformed),
	validate_concept(C2_transformed),
	/*b*/
	nnf(and(C1,C2),Prop_to_add_in_Abox),
	concat(Abi,[some(X,Prop_to_add_in_Abox)],Abi1).
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
 *  remplacer de manière récursive les identificateurs de concepts complexes par leur
définition
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

/*****************************************************/
/*Partie 3 : Tri et resolution */
/*****************************************************/
troisieme_etape(Abi,Abr) :-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
  resolution(Lie,Lpt,Li,Lu,Ls,Abr),
	nl,
	write('Youpiiiiii, on a demontre la proposition initiale !!!').


/*****************************************************/
/*tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls)*/
/*****************************************************/
/*traitement des litteraux*/
tri_Abox([],[],[],[],[],[]).
tri_Abox([(I,C)],Lie,Lpt,Li,Lu,[(I,C)|Ls]):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls), literal(C), iname(I).
tri_Abox([(I,C)|Abi],Lie,Lpt,Li,Lu,[(I,C)|Ls]):-
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
tri_Abox([inst(I,all(R,C))],[(I,all(R,C))|Lie],Lpt,Li,Lu,Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),
	iname(I), concept(C), rname(R).
tri_Abox([inst(I,all(R,C))|Abi],[(I,all(R,C))|Lie],Lpt,Li,Lu,Ls):-
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

tri_Abox([inst(I,and(C1,C2))],Lie,Lpt,[(I,and(C1,C2))|Li],Lu,Ls):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls),iname(I), concept(C1), concept(C2).




/*****************************************************/
/*resolution(Lie,Lpt,Li,Lu,Ls,Abr)*/
/*****************************************************/
resolution([],[],[],[],Ls,[]).
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :-
	%complete_some(Lie,Lpt,Li,Lu,Ls,Abr),
	%transformation_and(Lie,Lpt,Li,Lu,Ls,Abr),
	transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).
   

complete_some(Lie,Lpt,Li,Lu,Ls,Abr) :-
	write('Lie'),
	nl,
	write(Lie),
	nl,
	write('Lpt'),
	nl,
	write(Lpt),
	nl,
	write('Li'),
	nl,
	write(Li),
	nl,
	write('Lu'),
	nl,
	write(Lu),
	nl,
	write('Ls'),
	nl,
	write(Ls),
	nl,
	write('Abr'),
	write(Abr).
	



tri_Abox([(I,C)],Lie,Lpt,Li,Lu,[(I,C)|Ls]):-
	tri_Abox([],Lie,Lpt,Li,Lu,Ls), literal(C), iname(I).
tri_Abox([(I,C)|Abi],Lie,Lpt,Li,Lu,[(I,C)|Ls]):-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	iname(I),
	literal(C).

/*****************************************************/
/* transformation_and(Lie,Lpt,[inst(I,and(C1,C2))|Li],Lu,Ls,Abr)*/
/*****************************************************/
%adds in Abox a:C1,a:C2 for every instance with an and


transformation_and(Lie,Lpt,[inst(I,and(C1,C2))|Li],Lu,Ls,Abr)  :- concat(Ls,[inst(I,C1),inst(I,C2)],Z1),transformation_and(Lie,Lpt,Li,Lu,Z1,Abr).
% si on trouve plus de (I,and(C1,C2), on change la Abox )
transformation_and(Lie,Lpt,[],Lu,Ls,Abr)  :- unique(Ls,UniqueLs),resolution(Lie,Lpt,[],Lu,UniqueLs,Abr).


/*****************************************************/
/* Test clash */
%si on trouve inst(a,C) et inst(a,nonC) dans la Abox, clash

%mettre en nnf pour les cas , exp (non(non(personne)))
/*****************************************************/
%exemple jeu de test (voir plus dans rapport ): testclash([inst(david,not(personne)),inst(david,personne)])
testclash([]).
testclash([inst(I,C1)|Ls]) :-nnf(not(C1),Z), \+ memberchk(inst(I,Z),Ls),!,testclash(Ls).



/*****************************************************/
/* transformation_or(Lie,Lpt,Li,[inst(I,or(C1,C2))|Lu],Ls,Abr)*/
%adds in Abox  a:C1,a:C2 for  and creates two branches of the table.
/*****************************************************/

/*transformation_or(Lie,Lpt,Li,[inst(I,or(C1,C2))|Lu],Ls,Abr) :- 

concat(Ls,[inst(I,C1)],Z1),unique(Z1,UniqueLs1),write(UniqueLs1),nl, 
concat(Ls,[inst(I,C2)],Z2),unique(Z2,UniqueLs2),write(UniqueLs2),nl,write(UniqueLs2),
resolution(Lie,Lpt,Li,[],UniqueLs1,Abr),
resolution(Lie,Lpt,Li,[],UniqueLs2,Abr),
transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).



transformation_or(Lie,Lpt,Li,[],Ls,Abr) :- write('we're done lol).
	*/