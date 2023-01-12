%:- use_module(library(semweb/rdf_db)).
%:- use_module(library(semweb/rdf_ntriples)).
%:- use_module(library('semweb/rdf_persistency')).

:- dynamic isFinished/1.
:- dynamic subClassGraph/2.
:- dynamic subPropertyGraph/2.
:- dynamic domainGraph/2.
:- dynamic rangeGraph/2.
:- dynamic typeGraph/2.
:- dynamic triple/3.
:- dynamic newTypeGraph/2.
:- dynamic rdf/3.

inputPath( 'Encoded_LUBM1000/' ).

isFinished(false).

% Rule1
% It is a transitive rule so we will run it iteratively
rule( subClassTransitive ) :-
    subClassGraph( C1, C2 ),
    subClassGraph( C2, C3 ),
    C1 \== C3,
    \+ subClassGraph( C1, C3 ),
    assert( subClassGraph(C1, C3) ),
    assert( isFinished(true) ),
    fail.
rule( subClassTransitive ) :-
    isFinished(true),
    retractall( isFinished(true) ),
    rule( subClassTransitive ),
    fail.
rule( subClassTransitive ) :- !.

% Rule2
% It is also a transitive so we will run it
rule( subPropertyTransitive ) :-
    subPropertyGraph( P1, P2 ),
    subPropertyGraph( P2, P3 ),
    P1 \== P3,
    \+ subPropertyGraph( P1, P3 ),
    assert( subPropertyGraph( P1, P3 ) ),
    assert( isFinished(true) ),
    fail.
rule( subPropertyTransitive ) :-
    isFinished(true),
    retractall( isFinished(true) ),
    rule( subPropertyTransitive ),
    fail.
rule( subPropertyTransitive ) :- !.

% Rule3
rule( propertyInheritance ) :-
    subPropertyGraph( P, Q ),
    rdf( X, P, Y ),
    \+ rdf( X, Q, Y ),
    assert(rdf( X, Q, Y )),
    fail.
rule( propertyInheritance ) :- !.

% Rule4
rule( domain ) :-
    domainGraph( P, C ),
    rdf( X, P, Y ),
    \+ typeGraph( X, C ),
    assert( typeGraph( X, C ) ),
    fail.
rule( domain ) :- !.

% Rule5
rule( range ) :-
    rangeGraph( P, R ),
    rdf( S, P, O ),
    \+ typeGraph( O, R ),
    assert( typeGraph( O, R ) ),
    fail.
rule( range ) :- !.

% Rule6
rule( subClassInheritance ) :-
    typeGraph( A, X ),
    subClassGraph( X, Y ),
    \+ typeGraph( A, Y ),
    assert( typeGraph( A, Y ) ),
    fail.
rule( subClassInheritance ) :- !.

run_rule( subClassTransitive, NumberOfTriples, Time ) :-
    aggregate_all( count, subClassGraph(_,_), L1 ), % number of triples
    statistics( walltime, [Start,_] ),      % get the system time
    rule( subClassTransitive ),
    statistics( walltime, [End,_] ),
    aggregate_all( count, subClassGraph(_,_), L2 ),
    Time is End - Start,
    NumberOfTriples is L2 - L1,
    format( 'subClassTransitive rule : ~d triples inferred in ~3d sec', [NumberOfTriples, Time] ), nl.

run_rule( subPropertyTransitive, NumberOfTriples, Time ) :-
    aggregate_all( count, subPropertyGraph(_,_), L1 ), % number of triples
    statistics( walltime, [Start,_] ),      % get the system time
    rule( subPropertyTransitive ),
    statistics( walltime, [End,_] ),
    aggregate_all( count, subPropertyGraph(_,_), L2 ),
    Time is End - Start,
    NumberOfTriples is L2 - L1,
    format( 'subPropertyTransitive rule : ~d triples inferred in ~3d sec', [NumberOfTriples, Time] ), nl.

run_rule( propertyInheritance, NumberOfTriples, Time ) :-
    aggregate_all( count, rdf(_,_,_), L1 ), % number of triples
    statistics( walltime, [Start,_] ),      % get the system time
    rule( propertyInheritance ),
    statistics( walltime, [End,_] ),
    aggregate_all( count, rdf(_,_,_), L2 ),
    Time is End - Start,
    NumberOfTriples is L2 - L1,
    format( 'propertyInheritance rule : ~d triples inferred in ~3d sec', [NumberOfTriples, Time] ), nl.

run_rule( domain, NumberOfTriples, Time ) :-
    aggregate_all( count, typeGraph(_,_), L1 ), % number of triples
    statistics( walltime, [Start,_] ),      % get the system time
    rule( domain ),
    statistics( walltime, [End,_] ),
    aggregate_all( count, typeGraph(_,_), L2 ),
    Time is End - Start,
    NumberOfTriples is L2 - L1,
    format( 'domain rule : ~d triples inferred in ~3d sec', [NumberOfTriples, Time] ), nl.

run_rule( range, NumberOfTriples, Time ) :-
    aggregate_all( count, typeGraph(_,_), L1 ), % number of triples
    statistics( walltime, [Start,_] ),      % get the system time
    rule( range ),
    statistics( walltime, [End,_] ),
    aggregate_all( count, typeGraph(_,_), L2 ),
    Time is End - Start,
    NumberOfTriples is L2 - L1,
    format( 'range rule : ~d triples inferred in ~3d sec', [NumberOfTriples, Time] ), nl.

run_rule( subClassInheritance, NumberOfTriples, Time ) :-
    aggregate_all( count, typeGraph(_,_), L1 ), % number of triples
    statistics( walltime, [Start,_] ),      % get the system time
    rule( subClassInheritance ),
    statistics( walltime, [End,_] ),
    aggregate_all( count, typeGraph(_,_), L2 ),
    Time is End - Start,
    NumberOfTriples is L2 - L1,
    format( 'subClassInheritance rule : ~d triples inferred in ~3d sec', [NumberOfTriples, Time] ), nl.

% preprocessing for the schema

preprocessing :-
    rdf( S, P, O ),
    ( P =:= 6 ->
        assert( subClassGraph( S, O ) ),
        retractall(rdf(S, P, O))
    ;   ( P =:= 35 ->
            assert( subPropertyGraph( S, O ) ),
            retractall(rdf(S, P, O))
        ;   ( P =:= 31 ->
                assert( domainGraph( S, O ) ),
                retractall(rdf(S, P, O))
             ;  ( P =:= 33 ->
                    assert( rangeGraph( S, O ) ),
                    retractall(rdf(S, P, O))
                ;   ( P =:= 2 ->
                        \+ typeGraph(S, O),
                        assert( typeGraph( S, O ) ),
                        retractall(rdf(S, P, O))
                    )
                )
            )
        )
    ),
    fail.
preprocessing :-
    % printing number of each property
    aggregate_all( count, subClassGraph(_,_), SubClass ), write(' Num of SubClassOf : '), write(SubClass), nl,
    aggregate_all( count, subPropertyGraph(_,_), SubProperty ), write(' Num of SubPropertyOf : '), write(SubProperty), nl,
    aggregate_all( count, domainGraph(_,_), NumDomain ), write(' Num of Domain : '), write(NumDomain), nl,
    aggregate_all( count, rangeGraph(_,_), NumRange ), write(' Num of Range : '), write(NumRange), nl,
    aggregate_all( count, typeGraph(_,_), NumType ), write(' Num of Type : '), write(NumType), nl,
    aggregate_all( count, rdf(_,_,_), NumOthers ), write(' Num of Others : '), write(NumOthers), nl, !.

load :-
    %set_prolog_stack( global, limit(64*10**9) ),
    %set_prolog_stack( global, min_free(4) ),
    inputPath( DirectoryPath ),
    ( exists_directory( DirectoryPath )
    ->    atom_concat( DirectoryPath, '*.pl', Dir ), % direcoty_path/*.nt
          expand_file_name( Dir, FilePaths ),    % get all *.nt files within a directory
          attach_files( FilePaths )
    ;     format( '~s does not exist \n', [DirectoryPath] )
    ), !.
attach_files([File|List]) :-
    write(File), nl, !,
    read_data(File), !,
    attach_files(List), !.
attach_files(_) :- !.
    
read_data(File) :-
    open(File, read, Fd), !,
    read(Fd, First), !,
    read_data(First, Fd), !,
    close(Fd).
read_data(end_of_file, _) :- !.
read_data(Term, Fd) :-
    assert(Term), !,
    read(Fd, Next), !,
    read_data(Next, Fd), !.
    
go :-
    load,
    aggregate_all( count, rdf(_,_,_), FirstTriplesNum ),
    format( '~d Triples have been uploaded ', [FirstTriplesNum] ), nl, nl,
    write( 'Preprocessing... ' ), nl, nl,
    statistics( walltime, [Start,_] ),
    preprocessing,
    statistics( walltime, [End,_] ),
    PreProcessTime is End - Start,
    format( 'preprocessing time : ~3d sec', [PreProcessTime] ), nl,
    write( 'Inferring... ' ), nl, nl,
    run_rule( subClassTransitive, Num1, Time1 ),
    run_rule( subPropertyTransitive, Num2, Time2 ),
    run_rule( propertyInheritance, Num3, Time3 ),
    run_rule( domain, Num4, Time4 ),
    run_rule( range, Num5, Time5 ),
    run_rule( subClassInheritance, Num6, Time6 ), nl,
    Time is Time1 + Time2 + Time3 + Time4 + Time5 + Time6,
    NumOfTriples is Num1 + Num2 + Num3 + Num4 + Num5 + Num6,
    format( 'Total Running Time : ~3d sec', [Time] ), nl, nl,
    format( 'Number of Inferred Triples : ~d ', [NumOfTriples] ), nl,
    Num is NumOfTriples + FirstTriplesNum,
    write( 'Total Number of Triples after Inference : ' ), write( Num ), nl.
