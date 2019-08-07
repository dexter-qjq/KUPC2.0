module C-STMT-LABELED
     imports C-SYNTAX
     imports C-SYMBOLIC-VALUE-SYNTAX
     imports C-SYMLOC-SYNTAX

     syntax K ::= "get-Lvar" "(" CId "," Map ")"
     rule <k> Label(L:CId, K:K) => get-Lvar(L, Rho) ~> K ... </k>
          <curr-tu> CTu:String </curr-tu>
          <tu-id> CTu </tu-id>
          <labels> ... .Set => SetItem(L) </labels>
          <curr-program-loc> Loc:K </curr-program-loc>
          <curr-function> F:CId </curr-function>
          <label-stmt> ... .Map => L |-> K </label-stmt>
          <label-loc> _:Map(.Map => L |-> linfo(Loc,F)) </label-loc>
          <env> Rho:Map </env>
          <TuSet> Q:Set(.Set => SetItem(CTu)) </TuSet>
          when notBool(CTu in Q)

     rule <k> Label(L:CId, K:K) => get-Lvar(L, Rho) ~> K ... </k>
          <curr-tu> CTu:String </curr-tu>
          <tu-id> CTu </tu-id>
          <labels> ... .Set => SetItem(L) </labels>
          <curr-program-loc> Loc:K </curr-program-loc>
          <curr-function> F:CId </curr-function>
          <label-stmt> ... .Map => L |-> K </label-stmt>
          <label-loc> _:Map(.Map => L |-> linfo(Loc,F)) </label-loc>
          <env> Rho:Map </env>
          <TuSet> Q:Set </TuSet>
          when CTu in Q


     rule <k> get-Lvar(L:CId , _:CId |-> symVal _) ... </k>
          <curr-tu> CTu:String </curr-tu>
          <tu-id> CTu </tu-id>
          <label-type> Rho:Map(.Map => L |-> LabelTM(.Map)) </label-type>
          when notBool (L in keys(Rho))

     rule <k> get-Lvar(L:CId , (X:CId |-> symVal => .Map ) _) ... </k>
          <curr-tu> CTu:String </curr-tu>
          <tu-id> CTu </tu-id>
          <types> ... X |-> K:K ... </types>
          <label-type> ... L |-> LabelTM(_:Map(.Map => X |-> K)) ... </label-type>

     rule <k> get-Lvar(_, (_:CId |-> (_:Int @ _:Duration) => .Map) _ ) ... </k>
     rule <k> get-Lvar(_, .Map) => . ... </k>

//     rule [skip-label]: 
//          Label(_, K:K) => K
//          [structural]
     rule [case-fall-through]:
          Case(_, _, Exp:K, Stmt:K) => Computation(Exp) ~> Stmt
          [structural] 
     rule [default-fall-through]:
          Default(_, K:K) => K
          [structural] 
endmodule
