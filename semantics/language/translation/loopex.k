require "configuration.k"
require "syntax.k"

module C-LOOPEX
	imports C-SYNTAX
	imports C-CONFIGURATION
	imports C-STMT-LABELED
	imports C-TYPING-SYNTAX

	syntax K ::= "l-struct" "(" String "," CId ")"
			   | "con-struct" "(" String "," CId "," K ")"
			   | "con-function" "(" String "," CId "," K ")"
			   | "ex-change" "(" K  "," K ")"
			   | "replace" "(" String "," K ")"
			   | "replace-body" "(" String "," CId "," CId "," K ")"			//Tu, label id, function id, while loop body
         | "hellotu" "(" String ")"

  rule <k> (.K => hellotu(Tu)) ~> LoopExtract ... </k>
       <TuSet> ... SetItem(Tu:String) => .Set </TuSet>

	rule <k> (.K => l-struct(Tu,L:CId) ) ~> hellotu(Tu:String) ... </k>
     <tu-id> Tu </tu-id>
		 <labels> SetItem(L) => .Set ... </labels>

	rule <k> hellotu(Tu:String) => . ... </k>
     <tu-id> Tu </tu-id>
		 <labels> .Set </labels>	

  rule <k> LoopExtract => . ... </k>
       <TuSet> .Set </TuSet>

// declare the local state struct global named after (looplabel + "_xs")
	rule <k> l-struct(Tu:String, Identifier(S:String)) => 
			 con-struct(Tu, Identifier(S),
			 	OnlyTypedef( Specifier(list(ListItem(StructDef(Identifier( S +String "_xs"), 
			 			list(.List) 
			 			)))))
			 	) ... </k>
     <tu-id> Tu </tu-id>
		 <label-type> Rho:Map </label-type>
		 <label-copy> _ => Rho </label-copy>

	rule <k> con-struct(Tu:String, L:CId, OnlyTypedef( Specifier(list(ListItem(StructDef(_, list( _(.List =>
				 ListItem(FieldGroup ( Specifier ( list ( ListItem(Float) ) ) , 
              	 list ( ListItem(FieldName ( Name ( X , 
                 PointerType ( Specifier ( list ( .List ) ) , JustBase ) ) )) ) )) 
				 )))))))
				 ) ... </k>
     <tu-id> Tu </tu-id>
		 <label-type> ... L |-> LabelTM( (X:CId |-> t(.Set,float) => .Map)_) ... </label-type>

	rule <k> con-struct(Tu:String, L:CId, OnlyTypedef( Specifier(list(ListItem(StructDef(_, list( _(.List =>
				 ListItem(FieldGroup ( Specifier ( list ( ListItem(Int) ) ) , 
              	 list ( ListItem(FieldName ( Name ( X , 
                 PointerType ( Specifier ( list ( .List ) ) , JustBase ) ) )) ) )) 
				 )))))))
				 ) ... </k>
     <tu-id> Tu </tu-id>
		 <label-type> ... L |-> LabelTM( (X:CId |-> t(.Set,int) => .Map)_) ... </label-type>

	rule <k> con-struct(Tu:String, L:CId, OnlyTypedef( Specifier(list(ListItem(StructDef(_, list( _(.List =>
				 ListItem(FieldGroup ( Specifier ( list ( ListItem(Bool) ) ) , 
              	 list ( ListItem(FieldName ( Name ( X , 
                 PointerType ( Specifier ( list ( .List ) ) , JustBase ) ) )) ) )) 
				 )))))))
				 ) ... </k>
     <tu-id> Tu </tu-id>
		 <label-type> ... L |-> LabelTM( (X:CId |-> t(.Set,bool) => .Map)_) ... </label-type>

	rule <k> con-struct(Tu:String, Identifier(S:String), K:K) => K ~> con-function(Tu, Identifier(S:String),
			  FunctionDefinition ( SingleName ( Specifier ( list ( ListItem(
              Int) ) ) , Name ( Identifier ( S +String "_extract" ) , Prototype ( 
              JustBase , list ( ListItem(SingleName ( Specifier ( list ( 
              ListItem(Int) ) ) , Name ( Identifier ( "ret" ) , PointerType ( 
              Specifier ( list ( .List ) ) , JustBase ) ) )) ListItem(
              SingleName ( Specifier ( list ( ListItem(StructRef ( Identifier 
              ( S +String "_xs" ) )) ) ) , Name ( Identifier ( "xt" ) , PointerType ( 
              Specifier ( list ( .List ) ) , JustBase ) ) )) ) , false ) ) ) ,
              Block ( I , list ( L1) , list (.List)))) ... </k>
     <tu-id> Tu </tu-id>
     <patch-tu> .Set </patch-tu>
		 <label-type> ... Identifier(S:String) |-> LabelTM( .Map ) ... </label-type>
		 <label-stmt> ... Identifier(S:String) |-> (CodeLoc( BlockStatement (Block (I:Int, list(L1:List), K2:K)), _) => K2)  ... </label-stmt>

  rule <k> con-struct(Tu:String, Identifier(S:String), K:K) => K ~> con-function(Tu, Identifier(S:String),
        FunctionDefinition ( SingleName ( Specifier ( list ( ListItem(
              Int) ) ) , Name ( Identifier ( S +String "_extract_New" ) , Prototype ( 
              JustBase , list ( ListItem(SingleName ( Specifier ( list ( 
              ListItem(Int) ) ) , Name ( Identifier ( "ret" ) , PointerType ( 
              Specifier ( list ( .List ) ) , JustBase ) ) )) ListItem(
              SingleName ( Specifier ( list ( ListItem(StructRef ( Identifier 
              ( S +String "_xs" ) )) ) ) , Name ( Identifier ( "xt" ) , PointerType ( 
              Specifier ( list ( .List ) ) , JustBase ) ) )) ) , false ) ) ) ,
              Block ( I , list ( L1) , list (.List)))) ... </k>
     <tu-id> Tu </tu-id>
     <patch-tu> SetItem(Tu) </patch-tu>
     <wanted> ... .Set => SetItem(Identifier(S +String "_extract_New")) </wanted>
     <label-type> ... Identifier(S:String) |-> LabelTM( .Map ) ... </label-type>
     <label-stmt> ... Identifier(S:String) |-> (CodeLoc( BlockStatement (Block (I:Int, list(L1:List), K2:K)), _) => K2)  ... </label-stmt>



 rule <k> con-struct(Tu:String,X:CId, _) => hellotu(Tu) ... </k> 
      <tu-id> Tu </tu-id>
      <label-stmt> ... X |-> CodeLoc( Nop , _) ... </label-stmt>




// rewrite loop body => declare a function 
// break => return 0
// continue => return 1 
// return V => computation(:=) return 2
// CId => **identifier(xt).CId
	
	syntax K ::= "ex-changeB" "(" K "," List ")"
	rule <k> (.K => ex-change(K,.K)) ~> con-function(Tu:String, L:CId, _) ... </k>
     <tu-id> Tu </tu-id>
		 <label-stmt> ... L |-> list((ListItem(CodeLoc(K:K,_)) => .List)_) ... </label-stmt>

	rule <k> ex-change( K:K => .K , .K => K) ... </k>				[owise]

	rule <k> (.K => ex-changeB(K2,.List)) ~> ex-change( IfThenElse((K:K => .K),(BlockStatement(Block(I:Int, K1:K, K2:K)) => .K) ,_), 
										.K => IfThenElse(K,BlockStatement(Block(I, K1, list(.List))),.K)) ... </k>
	rule <k> (.K => ex-changeB(K2,.List)) ~> ex-change(IfThenElse(_, .K,(BlockStatement(Block(I:Int, K1:K, K2:K)) => .K)) , 
										 IfThenElse(_,_,(.K => BlockStatement(Block(I, K1, list(.List)))) )) ... </k>

	rule <k> ex-changeB(list( (ListItem(CodeLoc ( Break , Loc:K )) => .List) _ ), 
					    _ (.List => ListItem(CodeLoc(Return ( tv ( 0 , t ( .Set , int ) ) ), Loc)))    
					 ) ... </k>
	rule <k> ex-changeB(list( (ListItem(CodeLoc ( Continue , Loc:K )) => .List) _ ), 
						_ (.List => ListItem(CodeLoc(Return ( tv ( 1 , t ( .Set , int ) ) ), Loc)))
					 ) ... </k>
	rule <k> ex-changeB(list( (ListItem(CodeLoc ( Return ( K1:K ) , Loc:K )) => .List) _ ), 
						_ (.List => ListItem(CodeLoc(Computation ( * Identifier ( "ret" ) := K1),Loc))
								    ListItem(CodeLoc(Return ( tv ( 2 , t ( .Set , int ) ) ), Loc)))
					 ) ... </k>

	rule <k> ex-changeB(list((ListItem(K1:K) => .List)_),_(.List => ListItem(K1))) ... </k>				[owise]

	rule <k> (ex-changeB(list(.List), L:List) => .K) ~> ex-change(_,IfThenElse(_,BlockStatement(Block(_, _, list(.List => L))),.K)) ... </k>

	rule <k> (ex-changeB(list(.List), L:List) => .K) ~> ex-change(_,IfThenElse(_,BlockStatement(_),BlockStatement(Block(_, _, list(.List => L))))) ... </k>

	//termination 
	rule <k> ex-change((IfThenElse(.K,.K,.K) => .K) ,_ ) ... </k>

	rule <k> (ex-change(.K,K:K) => .K) ~> con-function(_, _:CId, FunctionDefinition(_,Block(_,_,list(_ (.List => ListItem(CodeLoc(K,Loc))))))) ... </k>
		 <curr-program-loc> Loc:CabsLoc </curr-program-loc>

  // return 1 at the end
  syntax K ::= "con-functionB" "(" String "," CId ","  K ")"
	rule <k> con-function(Tu, L:CId, FunctionDefinition(K1:K,Block(K2:K,K3:K,list(Ls:List)))) =>
           con-functionB(Tu, L, FunctionDefinition(K1,Block(K2,K3,list(Ls ListItem(CodeLoc(Return(tv ( 1 , t ( .Set , int ) )) ,Loc)))))) ... </k>
       <label-stmt> ... L |-> list(.List) ... </label-stmt>
       <tu-id> Tu:String </tu-id>
       <curr-program-loc> Loc:CabsLoc </curr-program-loc>

  rule <k> con-functionB(Tu:String,L:CId,K:K) =>  K ~> replace(Tu, L) ... </k>


	rule <k> replace(Tu, L:CId) => replace-body(Tu, L, F, K1)... </k>
       <tu-id> Tu:String </tu-id>
		   <label-loc> ... L |-> linfo( CabsLoc(Tu,_,_,_), F:CId) ... </label-loc>
         <goto-map>... 
              F:CId |-> map( (funLabel(F) |-> gotoObject(_,_,Block(_,_,K1:K => list(.List)) ~> _,_,_)) (L |-> _  => .Map ) ) 
         ...</goto-map>

    rule <k> replace-body(Tu:String, _, F:CId , list((ListItem( K:K )=> .List ) _)) ... </k>
    	 <tu-id> Tu </tu-id>
    	 <goto-map> ... 
    	 	  F:CId |->map( funLabel(F) |-> gotoObject(_,_,Block(_,_, list(_(.List => ListItem(K)))) ~> _,_,_)) 
         ...</goto-map> 						
    	 [owise]

   	syntax K ::= "rep-var" "(" String "," CId "," CId "," K ")"
   			   | "change-body" "(" String "," CId "," CId "," K ")"
   	// type of retval should be same as return value curr-function
   	// additional declaration xt, retval and code 
    rule <k> (.K => rep-var(Tu, Identifier(La), F, LabelTM(Rho))) ~> replace-body(Tu:String, Identifier(La:String), F:CId , list(ListItem( CodeLoc(While (_,_),_) ) _)) ... </k>
    	 <tu-id> Tu </tu-id>
    	 <goto-map> ... 
    	 	  F:CId |-> map( funLabel(F) |-> gotoObject(_,_,Block(_,_, list(_(.List => 
    	 	  	ListItem( CodeLoc ( DeclarationDefinition ( InitNameGroup (
                   Specifier ( list ( ListItem(StructRef ( Identifier ( 
                   La +String "_xs" ) )) ) ) , list ( ListItem(InitName ( Name ( 
                  Identifier ( "xt" ) , JustBase ) , NoInit )) ) ) ) , Loc ))
				ListItem(CodeLoc ( 
                  DeclarationDefinition ( InitNameGroup ( Specifier ( list ( 
                  ListItem(Int) ) ) , list ( ListItem(InitName ( Name ( 
                  Identifier ( "retval" ) , JustBase ) , NoInit )) ) ) ) , Loc))
				ListItem(CodeLoc ( 
                  DeclarationDefinition ( InitNameGroup ( Specifier ( list ( 
                  ListItem(Int) ) ) , list ( ListItem(InitName ( Name ( 
                  Identifier ( "code" ) , JustBase ) , NoInit )) ) ) ) , Loc ))
    	 	  ))) ~> _,_,_)) 
         ...</goto-map>
         <curr-program-loc> Loc:CabsLoc </curr-program-loc>
         <label-copy> ... Identifier(La) |-> LabelTM(Rho:Map) ... </label-copy> 


// initialize the structutal variable 
    rule <k> rep-var(Tu:String, _,F:CId, LabelTM( (X:CId |-> _ => .Map) _ )) ... </k>
    	 <tu-id> Tu </tu-id>
    	 <goto-map> ...
    	 		F |-> map ( funLabel(F) |-> gotoObject(_,_,Block(_,_, list(_ (.List => 
    	 			ListItem(CodeLoc ( Computation ( Identifier ( "xt" ) . X := & X ), Loc ))
		 )   )) ~> _,_,_ ))
    	 ... </goto-map>
         <curr-program-loc> Loc:CabsLoc </curr-program-loc>

    rule <k> (rep-var(_,_,_,LabelTM(.Map)) => change-body(Tu,Identifier(La), F, K2)) ~> replace-body(Tu:String, Identifier(La:String), F:CId, list( (ListItem(CodeLoc(While(K1:K,K2:K),_)) => .List )_ )) ... </k>
		 <tu-id> Tu </tu-id>
    	 <goto-map> ... 
    	 	  F:CId |-> map( funLabel(F) |-> gotoObject(_,_,Block(_,_, list(_(.List => 
    	 	  	ListItem(CodeLoc(While(K1,.K),Loc))
    	 	  ))) ~> _,_,_)) 
         ...</goto-map>
         <curr-program-loc> Loc:CabsLoc </curr-program-loc>

    rule <k> change-body(Tu:String, Identifier(L:String), F:CId, _) => . ... </k>
		<tu-id> Tu </tu-id>
    	 <goto-map> ... 
    	 	  F:CId |-> map( funLabel(F) |-> gotoObject(_,_,Block(_,_, list(_ 
    	 	  	ListItem(CodeLoc(While(_,.K 
    	 	  		=> 
    	 	  	  BlockStatement ( 
                  Block ( 1110 , list ( .List ) , list ( 
                  ListItem(CodeLoc ( 
                  BlockStatement ( Block ( 1111 , list ( .List ) , list ( 
                  ListItem(CodeLoc ( Computation ( Identifier ( "code" ) := 
                  Call ( Identifier ( L +String "_extract" ) , list ( ListItem(& 
                  Identifier ( "retval" )) ListItem(& Identifier ( "xt" )) ) )
                   ) , Loc )) 
                   ListItem(CodeLoc ( 
                  IfThenElse ( Identifier ( "code" ) == tv ( 0 , t ( .Set , 
                  int ) ) , BlockStatement ( Block ( 1115 , list ( .List ) , 
                  list ( ListItem(CodeLoc ( Break , Loc )) ) ) ) , BlockStatement ( Block ( 1112 , list ( .List )
                   , list ( ListItem(CodeLoc ( IfThenElse ( Identifier ( 
                  "code" ) == tv ( 1 , t ( .Set , int ) ) , BlockStatement ( 
                  Block ( 1114 , list ( .List ) , list ( ListItem(CodeLoc ( 
                  Continue , Loc )) ) ) ) , 
                  BlockStatement ( Block ( 1113 , list ( .List ) , list ( 
                  ListItem(CodeLoc ( Return ( Identifier ( "retval" ) ) , 
                  Loc )) ) ) ) ) , Loc )) ) ) ) ) , Loc )
                  ) ) ) ) , Loc )) ) ) )	
    	 	  		),_))
    	 	  )) ~> _,_,_)) 
         ...</goto-map>
         <curr-program-loc> Loc:CabsLoc </curr-program-loc>

  // body replace termination
  rule <k> replace-body ( _, _, _, list ( .List ) ) => . ... </k>



endmodule 