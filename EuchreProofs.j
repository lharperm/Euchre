CONJECTUREPANEL Assignment
PROOF "S→R, Q∧S ⊢ Q→R"
INFER S→R,
     Q∧S 
     ⊢ Q→R 
FORMULAE
0 R,
1 Q,
2 Q∧S,
3 S,
4 Q→R,
5 S→R 
IS
SEQ (cut[B,C\3,4]) (LAYOUT "∧ elim" (0) ("∧ elim(R)"[A,B\1,3]) (hyp[A\2])) (cut[B,C\0,4]) ("→ elim"[A,B\3,0]) (hyp[A\5]) (hyp[A\3]) (cut[B,C\1,4]) (LAYOUT "∧ elim" (0) ("∧ elim(L)"[A,B\1,3]) (hyp[A\2])) ("→ intro"[A,B\1,0]) (hyp[A\0])
END
CONJECTUREPANEL Theorems
PROOF "¬¬P ⊢ P"
INFER ¬¬P 
     ⊢ P 
FORMULAE
0 ⊥,
1 ¬¬P,
2 ¬P,
3 P 
IS
SEQ ("contra (classical)"[A\3]) (cut[B,C\0,0]) ("¬ elim"[B\2]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0])
END
CONJECTUREPANEL Assignment
PROOF "P→T, ¬R, T→R ⊢ ¬P"
INFER P→T,
     ¬R,
     T→R 
     ⊢ ¬P 
FORMULAE
0 ⊥,
1 ¬R,
2 R,
3 T,
4 T→R,
5 P,
6 P→T,
7 ¬P,
8 ¬¬P 
IS
SEQ ("contra (classical)"[A\7]) (cut[B,C\5,0]) ("¬¬P ⊢ P"[P\5]) (cut[B,C\3,0]) ("→ elim"[A,B\5,3]) (hyp[A\6]) (hyp[A\5]) (cut[B,C\2,0]) ("→ elim"[A,B\3,2]) (hyp[A\4]) (hyp[A\3]) (cut[B,C\0,0]) ("¬ elim"[B\2]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0])
END
CONJECTUREPANEL Theorems
PROOF "P→Q ⊢ ¬Q→¬P"
INFER P→Q 
     ⊢ ¬Q→¬P 
FORMULAE
0 ⊥,
1 ¬Q,
2 Q,
3 P,
4 P→Q,
5 ¬P 
IS
SEQ ("→ intro"[A,B\1,5]) ("¬ intro"[A\3]) (cut[B,C\2,0]) ("→ elim"[A,B\3,2]) (hyp[A\4]) (hyp[A\3]) (cut[B,C\0,0]) ("¬ elim"[B\2]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0])
END
CONJECTUREPANEL Assignment
PROOF "¬S∧(¬R→T), ¬(R∧¬S) ⊢ T∨Q"
INFER ¬S∧(¬R→T),
     ¬(R∧¬S)
     ⊢ T∨Q 
FORMULAE
0 T,
1 Q,
2 T∨Q,
3 ¬R,
4 ¬R→T,
5 ⊥,
6 ¬(R∧¬S),
7 R∧¬S,
8 ¬S,
9 R,
10 ¬S∧(¬R→T),
11 ¬T→¬¬R 
IS
SEQ (cut[B,C\4,2]) (LAYOUT "∧ elim" (0) ("∧ elim(R)"[A,B\8,4]) (hyp[A\10])) (cut[B,C\11,2]) ("P→Q ⊢ ¬Q→¬P"[P,Q\3,0]) (cut[B,C\8,2]) (LAYOUT "∧ elim" (0) ("∧ elim(L)"[A,B\8,4]) (hyp[A\10])) (cut[B,C\3,2]) ("¬ intro"[A\9]) (cut[B,C\4,5]) (LAYOUT "∧ elim" (0) ("∧ elim(R)"[A,B\8,4]) (hyp[A\10])) (cut[B,C\8,5]) (LAYOUT "∧ elim" (0) ("∧ elim(L)"[A,B\8,4]) (hyp[A\10])) (cut[B,C\7,5]) ("∧ intro"[A,B\9,8]) (hyp[A\9]) (hyp[A\8]) (cut[B,C\5,5]) ("¬ elim"[B\7]) (hyp[A\7]) (hyp[A\6]) (hyp[A\5]) (cut[B,C\0,2]) ("→ elim"[A,B\3,0]) (hyp[A\4]) (hyp[A\3]) (cut[B,C\0,2]) (hyp[A\0]) (LAYOUT "∨ intro" (0) ("∨ intro(L)"[B,A\1,0]) (hyp[A\0]))
END
CONJECTUREPANEL Quiz
PROOF "P(x)→((T(x)∧Q(x))∨(T(x)∧¬S(x))), P(x) ⊢ T(x)∧P(x)"
INFER P(x)→((T(x)∧Q(x))∨(T(x)∧¬S(x))),
     P(x)
     ⊢ T(x)∧P(x)
FORMULAE
0 P(x),
1 T(x),
2 T(x)∧¬S(x),
3 ¬S(x),
4 T(x)∧Q(x),
5 Q(x),
6 T(x)∧Q(x)∨T(x)∧¬S(x),
7 T(x)∧P(x),
8 P(x)→(T(x)∧Q(x))∨(T(x)∧¬S(x)),
9 (T(x)∧Q(x))∨(T(x)∧¬S(x)),
10 P(x)→((T(x)∧Q(x))∨(T(x)∧¬S(x)))
IS
SEQ (cut[B,C\9,7]) ("→ elim"[A,B\0,9]) (hyp[A\8]) (hyp[A\0]) (cut[B,C\1,7]) ("∨ elim"[A,B,C\4,2,1]) (hyp[A\6]) (cut[B,C\1,1]) (LAYOUT "∧ elim" (0) ("∧ elim(L)"[A,B\1,5]) (hyp[A\4])) (hyp[A\1]) (cut[B,C\1,1]) (LAYOUT "∧ elim" (0) ("∧ elim(L)"[A,B\1,3]) (hyp[A\2])) (hyp[A\1]) ("∧ intro"[A,B\1,0]) (hyp[A\1]) (hyp[A\0])
END
CONJECTUREPANEL Quiz
PROOF "(P∨R)→T, (Q∨S)→T ⊢ (P∨R)∨(Q∨S)→T"
INFER (P∨R)→T,
     (Q∨S)→T 
     ⊢ (P∨R)∨(Q∨S)→T 
FORMULAE
0 T,
1 Q∨S,
2 Q∨S→T,
3 P∨R,
4 P∨R→T,
5 P∨R∨(Q∨S),
6 (P∨R)∨(Q∨S),
7 (Q∨S)→T,
8 (P∨R)→T 
IS
SEQ ("→ intro"[A,B\6,0]) ("∨ elim"[A,B,C\3,1,0]) (hyp[A\5]) (cut[B,C\0,0]) ("→ elim"[A,B\3,0]) (hyp[A\4]) (hyp[A\3]) (hyp[A\0]) (cut[B,C\0,0]) ("→ elim"[A,B\1,0]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0])
END
CONJECTUREPANEL Theorems
PROOF "P ⊢ ¬¬P"
INFER P 
     ⊢ ¬¬P 
FORMULAE
0 ⊥,
1 ¬P,
2 P 
IS
SEQ ("¬ intro"[A\1]) (cut[B,C\0,0]) ("¬ elim"[B\2]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0])
END
CONJECTUREPANEL Theorems
PROOF "P→Q, ¬Q ⊢ ¬P"
INFER P→Q,
     ¬Q 
     ⊢ ¬P 
FORMULAE
0 ⊥,
1 ¬Q,
2 Q,
3 P,
4 P→Q 
IS
SEQ ("¬ intro"[A\3]) (cut[B,C\2,0]) ("→ elim"[A,B\3,2]) (hyp[A\4]) (hyp[A\3]) (cut[B,C\0,0]) ("¬ elim"[B\2]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0])
END
CONJECTUREPANEL Assignment
PROOF "¬P→¬T, T∨Q, ¬Q∨P, P→R ⊢ R"
INFER ¬P→¬T,
     T∨Q,
     ¬Q∨P,
     P→R 
     ⊢ R 
FORMULAE
0 R,
1 P,
2 P→R,
3 ⊥,
4 ¬Q,
5 Q,
6 ¬P,
7 ¬T,
8 ¬¬P,
9 T,
10 ¬¬T,
11 T∨Q,
12 ¬Q∨P,
13 ¬P→¬T 
IS
SEQ ("∨ elim"[A,B,C\4,1,0]) (hyp[A\12]) ("∨ elim"[A,B,C\9,5,0]) (hyp[A\11]) (cut[B,C\10,0]) ("P ⊢ ¬¬P"[P\9]) (cut[B,C\8,0]) ("P→Q, ¬Q ⊢ ¬P"[P,Q\6,7]) (cut[B,C\1,0]) ("¬¬P ⊢ P"[P\1]) (cut[B,C\0,0]) ("→ elim"[A,B\1,0]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0]) (cut[B,C\5,0]) (hyp[A\5]) (cut[B,C\3,0]) ("¬ elim"[B\5]) (hyp[A\5]) (hyp[A\4]) ("contra (constructive)"[B\0]) (hyp[A\3]) (cut[B,C\0,0]) ("→ elim"[A,B\1,0]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0])
END
CONJECTUREPANEL Assignment
PROOF "R→T, S∧¬T, S∨Q ⊢ (Q∧¬R)∨(S∧¬R)"
INFER R→T,
     S∧¬T,
     S∨Q 
     ⊢ (Q∧¬R)∨(S∧¬R)
FORMULAE
0 S∧¬R,
1 Q∧¬R,
2 ¬R,
3 S,
4 (Q∧¬R)∨(S∧¬R),
5 R,
6 T,
7 S∧¬T,
8 ¬T,
9 R→T,
10 S∨Q 
IS
SEQ (cut[B,C\3,4]) (LAYOUT "∧ elim" (0) ("∧ elim(L)"[A,B\3,8]) (hyp[A\7])) (cut[B,C\8,4]) (LAYOUT "∧ elim" (0) ("∧ elim(R)"[A,B\3,8]) (hyp[A\7])) (cut[B,C\2,4]) ("P→Q, ¬Q ⊢ ¬P"[P,Q\5,6]) (cut[B,C\0,4]) ("∧ intro"[A,B\3,2]) (hyp[A\3]) (hyp[A\2]) (LAYOUT "∨ intro" (0) ("∨ intro(R)"[B,A\1,0]) (hyp[A\0]))
END
CONJECTUREPANEL Assignment
PROOF "(S→T), ¬(T∨Q), (Q→R) ⊢ ¬S"
INFER (S→T),
     ¬(T∨Q),
     (Q→R)
     ⊢ ¬S 
FORMULAE
0 ⊥,
1 ¬(T∨Q),
2 T∨Q,
3 T,
4 Q,
5 S,
6 S→T,
7 Q→R 
IS
SEQ ("¬ intro"[A\5]) (cut[B,C\3,0]) ("→ elim"[A,B\5,3]) (hyp[A\6]) (hyp[A\5]) (cut[B,C\2,0]) (LAYOUT "∨ intro" (0) ("∨ intro(L)"[B,A\4,3]) (hyp[A\3])) (cut[B,C\0,0]) ("¬ elim"[B\2]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0])
END
CONJECTUREPANEL Quiz
PROOF "P, Q, R ⊢ S→((P∧¬Q)∨(¬P∧R))∧((P∧¬Q)∨(¬P∧R))→S"
INFER P,
     Q,
     R 
     ⊢ S→((P∧¬Q)∨(¬P∧R))∧((P∧¬Q)∨(¬P∧R))→S 
FORMULAE
0 S,
1 ((P∧¬Q)∨(¬P∧R))∧((P∧¬Q)∨(¬P∧R)),
2 ((P∧¬Q)∨(¬P∧R))∧((P∧¬Q)∨(¬P∧R))→S,
3 Q,
4 P,
5 R 
IS
SEQ ("→ intro"[A,B\0,2]) ("→ intro"[A,B\1,0]) (hyp[A\0])
END
CONJECTUREPANEL Theorems
PROOF "P∨¬P"
INFER P∨¬P 
FORMULAE
0 ⊥,
1 ¬(P∨¬P),
2 P∨¬P,
3 P,
4 ¬P,
5 ¬(P∨¬P)
IS
SEQ ("contra (classical)"[A\2]) (cut[B,C\3,0]) ("contra (classical)"[A\3]) (cut[B,C\2,0]) (LAYOUT "∨ intro" (0) ("∨ intro(R)"[B,A\3,4]) (hyp[A\4])) (cut[B,C\0,0]) ("¬ elim"[B\2]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0]) (cut[B,C\2,0]) (LAYOUT "∨ intro" (0) ("∨ intro(L)"[B,A\4,3]) (hyp[A\3])) (cut[B,C\0,0]) ("¬ elim"[B\2]) (hyp[A\2]) (hyp[A\1]) (hyp[A\0])
END
