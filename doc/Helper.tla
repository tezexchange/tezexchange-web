------------------------------- MODULE Helper -------------------------------
EXTENDS Naturals, TLC

VARIABLES pick

Range(T) == {<<T[x], x>> : x \in DOMAIN T}
Pick(S) == CHOOSE s \in S : TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == 
  IF S = {} THEN value
  ELSE LET s == Pick(S)
       IN 
       IF Op(s[1], value) = Op(value, s[1])
       THEN SetReduce(Op, S \ {s}, Op(s[1], value)) 
       ELSE Assert(FALSE, "error")
       
Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)

=============================================================================
