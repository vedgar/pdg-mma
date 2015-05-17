(* ::Package:: *)

fQ@p:=True;fQ@q:=True;fQ@r:=True;fQ@s:=True
fQ[(konj|disj|kond|bik)[a_?fQ,b_?fQ]]:=True;fQ[neg[a_?fQ]]:=True
fQ@_:=False;ffQ@x_:=fQ@x\[Or]x===False
SetAttributes[set,{Flat,Orderless,OneIdentity}]
set[a_?fQ,a_]:=set@a;set[x:pp[m_Integer?Positive,a_?fQ],x_]:=set@x;set[Not,Not]:=set@Not
set[a_Closed,a_,___]:=$Failed@a
set[(pp|Closed)[m_,___],_[m_,___],___]:=$Failed@m;ded[_,x_$Failed,__]:=x
kond[a_,False]:=neg@a;konj[kond[p_,q_],kond[q_,p_]]:=bik[p,q]
d[p_?fQ]:=ded[set@p,set[],p,ax@p]
d[p_?fQ,i_Integer?Positive]:=ded[set[],set@pp[i,p],p,ax[i,p]]
d[_Integer?Positive,ded[pa_set,ta_set,a_?fQ,st1_],ded[pb_set,tb_set,b_?fQ,st2_]]:=ded[set[pa,pb],set[ta,tb],konj[a,b],If[Head@konj[a,b]===bik,ibik,ikonj][st1,st2,konj[a,b]]]
d[1,ded[p_set,t_set,konj[a_,b_]?fQ,st_]]:=ded[p,t,a,ekonj[st,a]]
d[2,ded[p_set,t_set,konj[a_,b_]?fQ,st_]]:=ded[p,t,b,ekonj[st,b]]
d[1,ded[p_set,t_set,bik[a_,b_]?fQ,st_]]:=ded[p,t,kond[a,b],ebik[st,kond[a,b]]]
d[2,ded[p_set,t_set,bik[a_,b_]?fQ,st_]]:=ded[p,t,kond[b,a],ebik[st,kond[b,a]]]
d[ded[p_set,set[pp[m_,a_?fQ],t___],b_?ffQ,st_],m_Integer?Positive]:=ded[p,set[t,Closed@m],kond[a,b],If[b===False,ineg,ikond][st,m,kond[a,b]]]
d[ded[p_set,t_set,a_?fQ,st_],b_?fQ]:=ded[p,t,disj[a,b],idisj[st,disj[a,b]]]
d[a_?fQ,ded[p_set,t_set,b_?fQ,st_]]:=ded[p,t,disj[a,b],idisj[st,disj[a,b]]]
d[ded[p_set,t_set,disj[a_,b_]?fQ,st1_],ded[pa_set,set[pp[m_Integer?Positive,a_],a2___],c_?ffQ,st2_],ded[pb_set,set[pp[n_Integer?Positive,b_],b2___],c_,st3_]]:=ded[set[p,pa,pb],set[t,a2,b2,Closed@m,Closed@n],c,edisj[st1,st2,st3,m,n,c]]
d[ded[p1_set,t1_set,a_?fQ,st1_],ded[p2_set,t2_set,neg@a_,st2_]]:=ded[set[p1,p2],set[t1,t2],False,eneg[st1,st2,False]]
d[ded[p1_set,t1_set,a_,st1_],ded[p2_set,t2_set,kond[a_,b_]?fQ,st2_]]:=ded[set[p1,p2],set[t1,t2],b,ekond[st1,st2,b]]
d[ded[p_set,t_set,neg@neg@a_?fQ,st_]]:=ded[p,set[t,Not],a,edneg[st,a]]
ppr@p:="P";ppr@q:="Q";ppr@r:="R";ppr@s:="S"
ppr@konj:="\[And]";ppr@disj:="\[Or]";ppr@kond:="\[Rule]";ppr@bik:="\[LeftRightArrow]"
ppr[h_[a_,b_]?fQ]:="("<>ppr@a<>ppr@h<>ppr@b<>")"
ppr[neg[a_?fQ]]:="\[Not]"<>ppr@a
qpr[a_?fQ]:=With[{p=ppr@a},If[StringTake[p,1]==="(",StringTake[p,{2,-2}],p]]
d[_Integer?Positive,ded[set@prem___?fQ,set[_Closed...,x:Not...],konkl_?fQ,st_]]:=Column@{Row@{Row[qpr/@{prem},","],If[Length@{x}==1," \[RightTee]' "," \[RightTee] "],qpr@konkl},graf@st}
d[x__ded]:=d[3,x]
qpr@pp[n_Integer?Positive,a_?fQ]:=Superscript[OverBar@qpr@a,n]
graf@ax@p_:=qpr@p;graf@ax[i_,p_]:=qpr@pp[i,p]
graf@ineg:="(I\[Not])";graf@ikond:="(I\[Rule])";graf@ikonj:="(I\[And])";graf@ibik:="(I\[LeftRightArrow])";graf@idisj:="(I\[Or])";graf@ax:=""
graf@eneg:="(E\[Not])";graf@ekond:="(E\[Rule])";graf@ekonj:="(E\[And])";graf@ebik:="(E\[LeftRightArrow])";graf@edisj:="(E\[Or])";graf@edneg:="(\[Not]\[Not])"
graf[x_[st__,m___Integer,rez_]]:=Rasterize@Grid@{{Column[{Grid[{graf/@{st}},Alignment->Bottom],qpr@rez},Center,Dividers->Center,BaselinePosition->({{2,1},Top}->Axis)],m,graf@x}}
qpr@Closed@n_:=Style[n,FontVariations->{"StrikeThrough"->True}]
qpr@$Failed@x_:=Style[ToString@x<>"?",{Red,Large}]
qpr[set[]]:=\[EmptySet];qpr[set[a__]]:=Row[qpr/@{a},","];qpr[False]:="\[UpTee]";qpr[Not]:="\[Not]\[Not]"
qpr@ded[a_set,b_set,c_?ffQ,st_]:=Row@{qpr@a," ; ",qpr@b," \[RightTee] ",qpr@c,"    ",graf@Head@st}
qpr@x_:=x;$PrePrint=qpr
rpq[x_String]:=With[{t=ToExpression@StringReplace[x,{"P"->"p","Q"->"q","R"->"r","S"->"s","\[And]"->" ~konj~ ","^"->" ~konj~ ","&"->" ~konj~ ","\[Or]"->" ~disj~ ","v"->" ~disj~ ","V"->" ~disj~ ","|"->" ~disj~ ","\[Not]"->"neg@","-"->"neg@", "!"->"neg@","\[Rule]"->" ~kond~ ","->"->" ~kond~ ",">"->" ~kond~ ","\[LeftRightArrow]"->" ~bik~ ","<->"->" ~bik~ ","<>"->" ~bik~ ","="->" ~bik~ "}]},t/;fQ@t]
d[f_String]:=d@rpq@f
d[f_String,i_Integer?Positive]:=d[rpq@f,i]
d[f_String,a_ded]:=d[rpq@f,a]
d[a_ded,f_String]:=d[a,rpq@f]
"d[$] uvo\:0111enje aksioma
d[$,i] uvo\:0111enje privremene pretpostavke
d[1,%] eliminacija konjunkcije ili bikondicionala, slijeva
d[2,%] eliminacija konjunkcije ili bikondicionala, zdesna
d[3,%,%] introdukcija konjunkcije ili bikondicionala
d[%,%,%] eliminacija disjunkcije
d[%,$] introdukcija disjunkcije, slijeva
d[$,%] introdukcija disjunkcije, zdesna
d[%,%] eliminacija negacije ili kondicionala
d[%,i] introdukcija negacije ili kondicionala
d[%] eliminacija dvostruke negacije
d[4,%] zavr\[SHacek]etak dokaza (final check)
    Redoslijed argumenata je vrlo bitan!
$ string (u navodnicima) koji predstavlja formulu (p,q,r,s;&,|,!,>,=;(,) i mnogi drugi)
% neki od prethodnih izlaza (%: prethodni, %%: pretprethodni,... ili %42: Out[42])
i prirodni broj (redni broj privremene pretpostavke)"
