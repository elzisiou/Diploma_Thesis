

:- use_module(library(pce)).
:- dynamic ypsos2/1, examined/1.


 ask_state(Name) :-
        new(D, dialog('Insert State')),
        send(D, append(new(NameItem, text_item(name)))),
        send(D, append(button(ok, message(D, return, NameItem?selection)))),
        send(D, append(button(cancel, message(D, return, @nil)))),
        send(D, default_button(ok)),
        send(D, append(button(create_world, and(message(@prolog, create_world))))),
        get(D, confirm, Rval),
        free(D),
        Rval \== @nil,
        write(Rval),
        Name = Rval,
        write(Name).



%%%%%%%%%%%%%%%%%%%%%



:- dynamic bel/1, fact/1,  int/1, des/1,done/1.
:- dynamic(random_fact/3).
:- dynamic(fact_count/2).
:- op(1050, xfx, velos).
:- (op(1050, xfy, [->])).


    fact(block(a)).
    fact(block(b)).
    fact(block(c)).
    fact(block(d)).
    fact(block(e)).
    fact(block(f)).
    fact(block(g)).
    fact(color(a, red)).
    fact(color(b, blue)).
    fact(color(c, red)).
    fact(color(d, red)).
    %fact(color(e, green)).
    fact(color(f, red)).
    fact(color(g, purple)).

    fact(block(e))velos fact(color(e, green)).

%basic predicate
    fact(on(a,b)).
    fact(on(b,c)).
    fact(on(c,table)).
    fact(on(d,e)).
    fact(on(e,table)).
    fact(on(f,a)).
    fact(on(g,table)).
    fact(clear(table)).

%Defined predicate knowledge
    tower([X]):- fact(on(X, table)).
    tower([X, Y|T]):- fact(on(X, Y)), tower([Y|T]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                          %
%      BELIEFS-DESIRES-INTENTIONS                          %
%                                                          %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    bel(des(X)):- des(X).       /* Awareness of desires and intentions*/
    bel(int(X)):- int(X).

    %des(X):- bel(X).      /*An agent only inends to achieve some of its goals/desires*/
    %int(X):- des(X).      /*if the agent has a goal/desire X then he beleives that this is feasible*/


   %infer  -->
   bel(tower([X])):- bel(on(X,table)).
   bel(tower([X,Y|T])):- bel(on(X, Y)), bel(tower([Y|T])).
   %bel(tower([X, Y])):- bel(on(Y, table)), bel(on(X, Y)).
   bel(clear(X)):- bel(block(X)),not(bel(on(_Y,X))).

   bel(X):- done(X).

    main:-
      write('Enter a state of desires in a [ ] followed by a full stop: '), nl,
      read(State),
      write('state : '),
      write(State),
      nl,
      myselect(State),!,
      write('Protheseis toy praktora me vash tis epithumies tou : '),nl,
      forall(int(X),write(X )),
      nl,
      prepare_randomization_metadata(int(X)),
      write('Enter the type of agent commitment type 1 for blindly commited, 2 for single-minded or 3 for open-minded  followed by a full stop : '),
      read(Type1),
      about_agent(Type1),
      nl,
      write('Protheseis toy praktora efoson exei eksetasei tis epithumies tou : '),nl,
      forall(int(X),write(X )).






   myselect(Initial):- select(Xvalue, Initial, Rest), (
       (functor(Xvalue,on,2),arg(1,Xvalue,X),arg(2,Xvalue,Y),assert(des(on(X,Y))),assert(int(put_on(X,Y))));
       (functor(Xvalue,color,1),assert(des(Xvalue)),assert(int(Xvalue)));
       (functor(Xvalue,color,2),arg(1,Xvalue,X),arg(2,Xvalue,Y),assert(des(color(X,Y))),assert(int(change_color(X,Y))));
       (functor(Xvalue,clear_off,1),assert(des(Xvalue)),assert(int(Xvalue)));
       (Xvalue=..[tower,([X,Y])],assert(des(Xvalue)),assert(int(create_tower(X,Y))));
       (Xvalue=..[tower,([X,Y|T])],assert(des(Xvalue)),assert(int(establish_three(X,Y,T)))), write('bla ')),
       myselect(Rest),write('bla2 ').
   myselect([]).

   about_agent(Type):-(Type== 1, forall(int(X),(get_random_pred(int, Fact),arg(1,Fact,Y),blind_commit(Y))));(Type== 3, forall(int(X),(get_random_pred(int, Fact),arg(1,Fact,Y),open_minded(Y)))); (Type== 2, forall(int(X),(get_random_pred(int, Fact),arg(1,Fact,Y),single_minded(Y))),single_minded2).





   blind_commit(X):-
          write('sto blindly_committed '),
          nl,
          does(X).

   open_minded(X):-
           write('sto open_minded '),
           nl,
           does(X),
           retract_Int(X).
   single_minded(X):-
           write('sto single minded '),
           nl,
           does(X).
   single_minded2:-
            write('sto single minded2 '),
            nl,
            forall(int(X), open_minded(X)).




   does(Action):- int(Action),Action,intention_list(Action),retract(int(Action)),assert(succeeds(Action)) ; write('Den ekane thn action  '),assert(fails(Action)),nl.

   intention_list(Action):- done(Action),!;assert(done(Action)).

   retract_Int(X):-int(X),retract(int(X));true.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                          %
%       KD45 ---- weak S5 for beliefs                      %
%                                                          %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


    bel(Y):-velos(bel(X),bel(Y)), bel(X).        %modus ponens
    velos(bel(X),bel(Y)):-velos(fact(X),fact(Y)).

    bel(velos(X,Y)):-velos(bel(X),bel(Y)).   %K

    bel(X):- fact(X).                                    %NB
    bel(not_bel(X)):- write('AXIOM 5. '),not(bel(X)).    %----> 5.
    bel(bel(X)):- write('AXIOM 4. '),bel(X),!.             %---->4

    not_X(bel(not_X(X))):- write('AXIOM D. '), bel(X).      %----> D.   not(bel(not(X))):- bel(X).
    not_X(des(not_X(X))):- write('AXIOM D. '), des(X).        %----> D.   for desires
    not_X(int(not_X(X))):- write('AXIOM D. '), int(X).        %----> D.   for intentions


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                          %
%       ABOUT NEGATION                                     %
%                                                          %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



    not_X(X):- fact(X), !, fail; true.           %....not_X(X):- not(X).
    not_bel(X):- bel(X), !, fail; true.    %....not_bel(X):- not(bel(X)).


    bel(not_X(X)):- not(fact(X)).       %.....not(bel(X)) = bel(not(X))
    not_X(bel(X)):- bel(not_X(X)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                          %
%       ACTIONS                                            %
%                                                          %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    put_on(A,B) :-
     bel(on(A,B)).

    put_on(A,B) :-
     bel(not_X(on(A, B))),
     A \== table,
     A \== B,
     clear_off(A),        /* N.B. "action" used as precondition */
     clear_off(B),
     bel(on(A,X)),
     retract(fact(on(A,X))),
     assert(fact(on(A,B))),
     assert(move(A,X,B)).

    clear_off(table):-
     bel(clear(table)).    /* Means there is room on table */

    clear_off(A) :-      /* Means already clear */
     bel(clear(A)).

    clear_off(A) :-
     A \== table,
     bel(on(X,A)),
     clear_off(X),      /* N.B. recursion */
     retract(fact(on(X,A))),
     assert(fact(on(X,table))),
     assert(move(X,A,table)).

    color(Color):- list_colors(Color, L) ,select(X,L,Rest),!,put_on(X,table),select_pre(Rest,X).

    select_pre(L,X):- select(Y,L,Rest),put_on(Y,X),!,select_pre(Rest,Y).
    select_pre([],W):-clear_off(W).


   list_colors(P, L) :-
    list_colors(P, [], L).

   list_colors(P, Acc, L) :-
       bel(color(Block, P)),
        \+ member(Block, Acc), !,
        list_colors(P, [Block|Acc], L).
   list_colors(_, L, L).


   establish_three(X,Y,T):- put_on(X,table),put_on(Y,X),put_on(T,Y), clear_off(T).

   create_tower(X,Y):- put_on(Y,table), put_on(X,Y), clear_off(X).


   change_color(X,NewColor):- bel(color(X, Color)), Color \== NewColor ,retract(fact(color(X, Color))), assert(fact(color(X, NewColor))).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                          %
%       Random select                                      %
%                                                          %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  prepare_randomization_metadata(Goal) :-
    findall(Goal, Goal, Occurrances),
    prepare_randomization_metadata(Occurrances, 0),
    Goal =.. [Head|_],
    length(Occurrances, N),
    asserta(fact_count(Head, N)).

  prepare_randomization_metadata([], _).
  prepare_randomization_metadata([Goal|Goals], N) :-
    Goal =.. [Head|_],
    asserta(random_fact(Head, Goal, N)),
    N1 is N+1,
    prepare_randomization_metadata(Goals, N1), !.


  get_random_pred(Head, Pred) :-

    fact_count(Head, N),
    % pick a random number between 0 and the # of facts we have for this pred
    random(0, N, I),
    ((random_fact(Head, Pred, I), !,retract(random_fact(Head, Pred, I))); (aggregate_all(count, random_fact(X,Y,Z), Count),Count\==0,get_random_pred(Head, Pred))).


   :- nl,
   write('**************************************'), nl,
   write('** Enter <<instructions.>> ---->to see instructions **'), nl,
   write('**************************************'), nl,
   nl.

   instructions :-
        nl,
        write('Enter commands using standard Prolog syntax.'), nl,
        write('Available commands are:'), nl,
        write('world.                        -- to see the current state.'), nl, nl,
        write('main.                         -- to run the main program and enter state'),nl, nl,
        write('Accepted States : '),nl,
        write('color(Color).                       -- if Agent desires to create a tower with blocks with the same color.'), nl,
        write('color(Block,Color).                 -- if Agent desires to change the color of block.'), nl,
        write('clear_off(X).                       -- if Agent desires to clear a block.'), nl,
        write('on(X,Y).                            -- if Agent desires to move a block into another object(block or table).'), nl,
        write('tower([Block1,Block2|Block3]).      -- if Agent desires to establish Block1 on Block2 on Block3.'), nl,
        write('tower([Block1,Block2]).             -- if Agent desires to establish Block1 on Block2 .'), nl, nl,
        write('bel(X).                       -- to see agent�s beliefs.'),nl,
        write('des(X).                       -- to see agent�s desires.'), nl,
        write('int(X).                       -- to see agent�s intentions.'), nl,
        write('done(X).                      -- to see which intentions have been done.'), nl,
        nl.


   world:- forall(fact(on(X,Y)),write_state(X ,Y)).
   write_state(X,Y):- write('Block '),write(X),write(' on '),write(Y),nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
ypsos2(0).
:- pce_begin_class(kyvos(name, onwhat, color, pointX, pointY), object).
variable(name, name, both, "Name of the block").
variable(onwhat, string, both, "onwhat").
variable(color, string, both, "color").
variable(pointX, int, both, "PointX").
variable(pointY, int, both, "PointY").
initialise(P, Name:name, Onwhat:string, Color:string, PointX:int, PointY:int) :->
"Create kyvo"::
send(P, name, Name),
send(P, onwhat, Onwhat),
send(P, color, Color),
send(P, pointX, PointX),
send(P, pointY, PointY).
:- pce_end_class.

window:-   new(@p, picture('Demo Picture')),send(@p, open),send(@p, display,new(@table, box(1000,40)),point(0,800)),send(@table, fill_pattern, colour(brown)).


create_world:-
   free_XPCE,
   window,
   forall((fact(on(Block1,table)),bel(color(Block1,Color))),(new(@Block1, kyvos(Block1,table,Color,0,0)),world(Block1,table,Color))),
   forall(fact(on(Blocktable,table)),(forall((fact(on(Block1,Blocktable)),bel(color(Block1,Color))),(new(@Block1, kyvos(Block1,Blocktable,Color,0,0)),world(Block1,Blocktable,Color))))),
   forall((fact(on(Block1,Block2)),not(examined(fact(on(Block1,Block2)))),bel(color(Block1,Color))),(new(@Block1, kyvos(Block1,Block2,Color,0,0)),world(Block1,Block2,Color))).
   %forall((on(Block1,Block2),Block2\=='table',Block1\==Blocktable,color(Block1,Color)),world(Block1,Block2,Color)).

   
world(Block1,Block2,Color):-

    (Block2 == table,createontable(Block1),
    draw(Block1));
    (createonbox(Block1,Block2),draw(Block1));true.



createontable(Block1):-

      retract(ypsos2(Ypsos)),
      send(@Block1, pointX, Ypsos),
      send(@Block1, pointY, 700),
      YpsosNew is Ypsos+150,
      assert(ypsos2(YpsosNew)),
      list_examinedBLocks(Block1,table).

createonbox(Block1,Block2):-

      get(@Block2, pointX, Rval1),
      get(@Block2, pointY, Rval2),
      send(@Block1, pointX, Rval1),
      send(@Block1, pointY, Rval2-100),
      list_examinedBLocks(Block1,Block2).


      
draw(Block1):-
   get(@Block1, pointX, Rval1),
   get(@Block1, pointY, Rval2),
   get(@Block1, color, Color),
   name(Block1,NameBlock1),append("box",NameBlock1,F), name(Nameofbox,F),
   name(Block1,NameBlock1),append("block",NameBlock1,G), name(Nameofblock,G),
   send(@p, display,new(@Nameofbox, box(100,100)),point(Rval1,Rval2)),
   send(@p, display,new(@Nameofblock, text(Block1)), point(Rval1+20,Rval2+20)),
   send(@Nameofblock, font, font(times, bold, 18)),
   send(@Nameofbox, fill_pattern, colour(Color)).
   %send(@p, display, box(100,100),point(Rval1,Rval2)).




  list_examinedBLocks(Block1,Block2) :-
     assert(examined(fact(on(Block1,Block2)))).

 free_XPCE:-forall(fact(block(X)),(free(@p),free(@table),free(@X),name(X,NameBlock1),append("box",NameBlock1,F), name(Nameofbox,F),free(@Nameofbox),name(Block1,NameBlock1),append("block",NameBlock1,G), name(Nameofblock,G),free(@Nameofblock),retract(ypsos2(Ypsos)),assert(ypsos2(0)))),
    forall(examined(fact(on(Block1,Block2))),retract(examined(fact(on(Block1,Block2))))).
 

