header {* Abstract syntax for Hybrid CSP. *}

theory HHL
  imports  HCSP_Com
begin

consts spec :: "fform => proc => fform => fform => prop"   ("{_}_{_;_}" 80)
consts specP :: "fform => fform => proc => fform => fform => fform  => fform => prop"   ("{_, _}_{_, _ ; _, _}" 80)

(*Skip rule*)
axiomatization where
Skip : "|- ((l [=] (Real 0)) [-->] G) ==> {p} Skip {p; G}" 


(*Assignment rule*)
axiomatization where
Assign  :" [| ~inPairForm ([(e, f)], q); |-(p [-->] (substF ([(e, f)]) (q)))
        [&]   ((l [=] (Real 0)) [-->] G)|] ==>
       {p} (e := f) {q; G}"


(*Example*)
lemma "{WTrue} (RVar ''x'') := (Real 2) {((RVar ''x'') [=] (Real 2)); (l [=] (Real 0))}"
apply (cut_tac p = "WTrue" and e = "(RVar ''x'')" and f = "(Real 2)" and 
                q = "((RVar ''x'') [=] (Real 2))" and G = "(l [=] (Real 0))" in Assign, auto)
apply (rule Trans,auto)
done


(*Continuous rule*)
axiomatization where
Continue : "|- (Init [-->] F)
           [&] ((p [&] close(F) [&] close([~]b)) [-->] q)
           [&] ((((l [=] Real 0) [|] (high (close(F) [&] p [&] close(b)))) [&] Rg) [-->] G)
           ==> {Init [&] p} <F&&b> : Rg {q; G}"

(*Sequential rule*)
axiomatization where
Sequence : "[| {p} P {m; H}; {m} Q {q; G} |] ==>
             {p} P; (m, H); Q {q; H [^] G}" 
        

(*Conditional rule*)
axiomatization where
ConditionF : " [| |-(p [-->] [~] b); |- (p [-->] q); |- ((l [=] Real 0) [-->] G) |]
             ==> {p} IF b P {q; G}"
and
ConditionT :  "[| |-(p [-->] b); {p} P {q; G} |]
             ==> {p} IF b P {q; G}"
and
Condition : "[| {p [&] b} IF b P {q; G}; {p [&] ([~]b)} IF b P {q; G}|] 
             ==> {p} IF b P {q; G}"


(*Nondeterministic rule*)
axiomatization where
Nondeterministic :
"{p [&] b} P {q;G}
  ==> {p} NON i x : b P {q; G}"

(*Communication rule*)
(*H in the rule denotes the common interval range.*)
axiomatization where
Communication : "[| ~inPairForm ([(x, e)], ry);
                    {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                    |- (qx [-->] rx) [&] (qy [-->] (substF ([(x, e)]) (ry)));
                    |- ((Hx [^] (high (qx))) [-->] Gx) [&] ((Hy [^] (high (qy))) [-->] Gy);
                    |- ((((Hx [^] (high (qx))) [&] Hy) [|]((Hy [^] (high (qy))) [&] Hx)) [-->] H)
                 |]
              ==>   {px, py} ((Px; (qx, Hx); ch !! e) || (Py; (qy, Hy); ch ?? x)) {rx, ry; 
                    Gx [&] H, Gy [&] H}"

(*Communication interrupt rule*)
primrec contain :: "proc => proc => bool" where
"contain (Skip,p) = False" |
"contain (Stop,p) = False" |
"contain (x:=e,p) = False" |
"contain ((Ch!!e),p) = ((Ch!!e)=p)" |
"contain ((Ch??x),p) = ((Ch??x)=p)" |
"contain ((q;m;r),p) = False" |
"contain ((IF b q),p) = False" |
"contain ((NON i x : b q),p) = False" |
"contain ((q [[ r),p) = (if contain(q,p) then True else contain(r,p))" |
"contain ((q << r),p) = False" |
"contain ((q || r),p) = False" |
"contain ((q*),p) = False" |
"contain ((q**n),p) = False" |
"contain ((<F && b> : g),p) = False" |
"contain ((q |> b r),p) = False" |
"contain ((q [[> r),p) = False"

(**)
axiomatization where
CommunicationI1 : "[| ~inPairForm ([(x, e)], ry);
                    |- Hy [-->] H;
                    |- rg [-->] H[^]WTrue;
                    {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                    |- Init [&] pre [<->] qx;
                    |- pre [&] Init [&] b [-->] F;
                    |- (pre [&] close(F) [&] close(b)) [-->] rx;
                    |- (qy [&] pre [&] close(F) [&] close(b)) [-->] (substF ([(x, e)]) (ry));
                    |- (Hx [^] ((((l [=] Real 0) [|] (high (close(F) [&] pre [&] close(b)))) [&] H)) [-->] Gx);
                    |- Hy [-->] Gy;
                    |- Hx [-->] Hxm;
                    |- Hy [-->] Hym;
                    contain(P,(ch !! e))
                 |]
              ==>   {px, py} (( Px; (qx, Hxm); (<F && b> :rg) [[> P) || (Py; (qy, Hym); ch ?? x))
                    {rx, ry; Gx, Gy}"
axiomatization where
CommunicationI2 : "[| ~inPairForm ([(x, e)], ry);
                    |- Hy [-->] H;
                    |- rg [-->] H[^]WTrue;
                    {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                    |- Init [&] pre [<->] qx;
                    |- pre [&] Init [&] b [-->] F;
                    |- (qy [&] pre [&] close(F) [&] close(b)) [-->] (substF ([(x, e)]) (rx));
                    |- qy [-->] ry;
                    |- Hx [^] ((((l [=] Real 0) [|] (high (close(F) [&] pre [&] close(b)))) [&] H)) [-->] Gx;
                    |- Hy [-->] Gy;
                    |- Hx [-->] Hxm;
                    |- Hy [-->] Hym;
                    contain(P,(ch ?? x))
                 |]
              ==>   {px, py} (( Px; (qx, Hxm); (<F && b> :rg) [[> P) || (Py; (qy, Hym); ch !! e))
                    {rx, ry; Gx, Gy}"

(*Parallel rule*)
(*It is valid only when there are not communications occurring in P3 and P4.*)
axiomatization where
Parallel1: "[| {px, py} (Px || Py) {qx, qy; Hx, Hy}; {qx} Qx {rx; Gx}; {qy} Qy {ry; Gy} |]
           ==>  {px, py} ((Px; (qx, Hx); Qx) || (Py; (qy, Hy); Qy)) {rx, ry; Hx [^] Gx, Hy [^] Gy}"

(*It is valid only when there are no communications occurring in P1 and P2.*)
axiomatization where
Parallel2: "[| {px} Px {qx; Hx}; {py} Py {qy; Hy}|]
           ==> {px, py} (Px || Py) {qx, qy; Hx, Hy}"
(*It is valid in any case*)
axiomatization where
Parallel3: "[| {px, py} (Px || Py) {qx, qy; Hx[&](l[=](Real m)), Hy[&](l[=](Real m))};
               {qx, qy} (Qx || Qy) {rx, ry; Mx, My};
               |- (Hx[&](l[=](Real m))) [-->] HL;
               |- (Hy[&](l[=](Real m))) [-->] HR;
               |- ((Hx[&](l[=](Real m))) [^] Mx) [-->] Gx;
               |- ((Hy[&](l[=](Real m))) [^] My) [-->] Gy
            |]
           ==> {px, py} (Px;(qx,HL);Qx) || (Py;(qy,HR);Qy) {rx, ry; Gx, Gy}"

(*Repetition rule*)
axiomatization where
Repetition : "[| {px, py} (Px || Py) {px, py; Hx, Hy};
                 |- Hx [^] Hx [-->] Hx; |- Hy [^] Hy [-->] Hy|]
           ==>  {px, py} ((Px*) || (Py*)) {qx, qy; Hx, Hy} "

(*N times repetition request post and history holds for any middle state to ensure RepetitionG holds.*)
axiomatization where
RepetitionT1a : "{px, py} ((Px;M;Pz) || Py) {qx, qy; Hx, Hy}
           ==>  {px, py} (((Px**1);M;Pz) || Py) {qx, qy; Hx, Hy}" and
RepetitionTna : "[| {px, py} (((Px**m);(qx,H);Px;M;P) || Py) {qx, qy; Hx, Hy};
                 |- Hx [^] Hx [-->] Hx;
                 |- H [-->] Hx|]
           ==>  {px, py} (((Px**(m+1));M;P) || Py) {qx, qy; Hx, Hy}" and
RepetitionG : "[| {px, py} (Px**(m+1) || Py**(n+1)) {px, py; Hx, Hy};
                 |- Hx [^] Hx [-->] Hx; |- Hy [^] Hy [-->] Hy|]
           ==>  {px, py} ((Px* ) || (Py* )) {px, py; Hx, Hy} " and
RepetitionE : "[| {px, py} (((P;M;(Px**(n+1)));(qx,Hx);(Px* )) || Py) {qx, qy; Hx, Hy}|]
           ==>  {px, py} ((P;M;(Px* )) || Py) {qx, qy; Hx, Hy} "

(*Structure rule*)
axiomatization where
Structure : "{px, py} (Px || Py) {qx, qy; Hx, Hy}
           ==> {py, px} (Py || Px) {qy, qx; Hy, Hx}" and
structR : "{px, py} Q||((Px;Mx;Py);My;Pz) {qx, qy; Hx, Hy}
           ==> {px, py} Q||(Px;Mx;Py;My;Pz){qx, qy; Hx, Hy}" and
structL : "{px, py} ((Px;Mx;Py);My;Pz)||Q {qx, qy; Hx, Hy}
           ==> {px, py} (Px;Mx;Py;My;Pz)||Q{qx, qy; Hx, Hy}" and
structSkipL : "{px, py} (Skip;(px,l[=](Real 0));P)||Q {qx, qy; Hx, Hy}
           == {px, py} P||Q{qx, qy; Hx, Hy}" and
structSkipR : "{px, py} (P;(qx,Hx);Skip)||Q {qx, qy; Hx, Hy}
           == {px, py} P||Q{qx, qy; Hx, Hy}"


(*Consequence rule*)
axiomatization where
ConsequenceS : "[| {px} P {qx; Hx}; |- ((p [-->] px) [&] (qx [-->] q) [&] (Hx [-->] H))|]
            ==> {p} P {q; H}"
and
ConsequenceP : "[| {px, py} (Px || Py) {qx, qy; Hx, Hy}; 
                   |- ((p [-->] px) [&] (r [-->] py) [&] (qx [-->] q) [&] (qy [-->] s) 
                       [&] (Hx [-->] H) [&] (Hy [-->] G))|]
            ==> {p, r} (Px || Py) {q, s; H, G}"

(*important derived rules*)
lemma structSkipEL : "{px, py} (Skip;(px,l[=](Real 0));P)||Q {qx, qy; Hx, Hy}
           ==> {px, py} P||Q{qx, qy; Hx, Hy}"
apply (cut_tac px=px and py=py and P=P and Q=Q and qx=qx and qy=qy and Hx=Hx and Hy=Hy in structSkipL,auto)
done

lemma structSkipIL : "{px, py} P||Q{qx, qy; Hx, Hy}
           ==> {px, py} (Skip;(px,l[=](Real 0));P)||Q {qx, qy; Hx, Hy}"
apply (cut_tac px=px and py=py and P=P and Q=Q and qx=qx and qy=qy and Hx=Hx and Hy=Hy in structSkipL,auto)
done

lemma structSkipER : "{px, py} (P;(qx,Hx);Skip)||Q {qx, qy; Hx, Hy}
           ==> {px, py} P||Q{qx, qy; Hx, Hy}"
apply (cut_tac px=px and py=py and P=P and Q=Q and qx=qx and qy=qy and Hx=Hx and Hy=Hy in structSkipR,auto)
done

lemma structSkipIR : "{px, py} P||Q{qx, qy; Hx, Hy}
           ==> {px, py} (P;(qx,Hx);Skip)||Q {qx, qy; Hx, Hy}"
apply (cut_tac px=px and py=py and P=P and Q=Q and qx=qx and qy=qy and Hx=Hx and Hy=Hy in structSkipR,auto)
done

lemma RepetitionT1 : "{px, py} (Px || Py) {qx, qy; Hx, Hy}
           ==>  {px, py} (Px**1 || Py) {qx, qy; Hx, Hy}"
apply (rule structSkipER)
apply (rule RepetitionT1a)
apply (rule structSkipIR,auto)
done

lemma RepetitionTn : "[| {px, py} (((Px**m);(qx,H);Px) || Py) {qx, qy; Hx, Hy};
                 |- Hx [^] Hx [-->] Hx;
                 |- H [-->] Hx|]
           ==>  {px, py} (Px**(m+1) || Py) {qx, qy; Hx, Hy}"
apply (rule structSkipER)
apply (cut_tac H="H" in RepetitionTna,auto)
apply (rule structL)
apply (rule structSkipIR,auto)
done

lemma Parallel4: "[| {py} Py {qy; Hy[&](l[=](Real 0))};
               {qx, qy} (Qx || Qy) {rx, ry; Mx, My};
               |- (Hy[&](l[=](Real 0))) [-->] HR;
               |- ((Hy[&](l[=](Real 0))) [^] My) [-->] Gy
            |]
           ==> {qx, py} (Qx) || (Py;(qy,HR);Qy) {rx, ry; Mx, Gy}"
apply (rule structSkipEL)
apply (cut_tac m=0 and Hx="l [=] Real 0" in Parallel3,auto)
apply (rule Parallel2,auto)
apply (rule Skip)
(*1*)
apply (rule impR)
apply (rule conjR)
apply (rule basic)+
apply (rule impR)
apply (rule conjL)
apply (rule basic)
apply (rule impR)
apply (rule LC1)
apply (rule LL3a)
apply (rule basic)
done

lemma Parallel1a: "[| {px, py} (Px || Py) {qx, qy; Hx, Hy}; {qy} Qy {ry; Gy}; |- Hy [^] Gy [-->] G |]
           ==>  {px, py} ((Px) || (Py; (qy, Hy); Qy)) {qx, ry; Hx, G}"
apply (rule structSkipER)
apply (subgoal_tac "{px, py}(Px;(qx, Hx);Skip)||(Py;(qy, Hy);Qy){qx,ry; (Hx [^] l [=] Real 0), Hy [^] Gy}")
apply (cut_tac px=px and py=py and qx=qx and qy=ry and Hx="Hx [^] l [=] Real 0" and Hy="Hy [^] Gy" in ConsequenceP,auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule LL4)
apply (rule basic)
apply assumption
(*start*)
apply (cut_tac px=px and py=py and Px=Px and qx=qx and Hx="Hx" and Qx=Skip and Py=Py and qy=qy and Hy=Hy and Qy=Qy and rx=qx and ry=ry and Gx="(l [=] Real 0)" and Gy=Gy in Parallel1,auto)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
done

lemma CommunicationI1b : "[| ~inPairForm ([(x, e)], ry);
                    |- Hy [-->] H;
                    |- rg [-->] H[^]WTrue;
                    {py} ( Py) {qy; Hy}; 
                    |- Init [&] pre [<->] qx;
                    |- pre [&] Init [&] b [-->] F;
                    |- (pre [&] close(F) [&] close(b)) [-->] rx;
                    |- (qy [&] pre [&] close(F) [&] close(b) [-->] (substF ([(x, e)]) (ry)));
                    |- ((((l [=] Real 0) [|] (high (close(F) [&] pre [&] close(b)))) [&] H) [-->] Gx);
                    |- Hy [-->] Gy;
                    |- Hx [-->] Hxm;
                    |- Hy [-->] Hym;
                    contain(P,(ch !! e))
                 |]
              ==>   {qx, py} (((<F && b> :rg) [[> P) || (Py; (qy, Hym); ch ?? x))
                    {rx, ry; Gx, Gy}"
apply (rule structSkipEL)
apply (cut_tac Hx="l [=] Real 0" and Init=Init in CommunicationI1,auto)
apply (rule Parallel2,auto)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (cut_tac P="((l [=] Real 0 [|] high (close(F) [&] pre [&] close(b))) [&] H) [-->] Gx" in cut,auto)
apply (rule thinR,auto)
apply (rule impR)
apply (rule LL3a)
apply (rule impL)
apply (rule basic)+
apply (rule impR)
apply (rule basic)
done

lemma structSkipELR : "{px, py} Q||(Skip;(py,l[=](Real 0));P) {qx, qy; Hx, Hy}
           ==> {px, py} Q||P{qx, qy; Hx, Hy}"
apply (rule Structure)
apply (rule structSkipEL)
apply (rule Structure)
apply assumption
done

lemma CommunicationI1a : "[| ~inPairForm ([(x, e)], ry);
                       |- Init [&] pre [<->] px;
                       |- pre [&] Init [&] b [-->] F;
                       |- (pre [&] close(F) [&] close(b)) [-->] rx;
                       (*|- px [-->] rx;*)
                       |- py [&] pre [&] close(F) [&] close(b) [-->] (substF ([(x, e)]) (ry));
                       |- (l[=]Real 0) [-->] Gx;
                       |- (l[=]Real 0) [-->] Gy;
                       contain(Px,(ch !! e))|]
              ==>   {px, py} (((<F && b> :rg) [[> Px) || (ch ?? x)) {rx, ry; Gx, Gy}"
apply (rule structSkipEL)
apply (rule structSkipELR)
apply (cut_tac H="l [=] Real 0" and Hx="l [=] Real 0" in CommunicationI1,auto)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule RL3a)
apply (simp add: True_def)
apply (rule impR)
apply (rule basic)
apply (rule Parallel2)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule LL3a)
apply (rule conjL)
apply (rule thinL)
apply (cut_tac P="l [=] Real 0 [-->] Gx" in cut,auto)
apply (rule thinL)
apply (rule thinR,auto)
apply (rule impL)
apply (rule basic)+
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule basic)
done

lemma CommunicationI2a : "[| ~inPairForm ([(x, e)], ry);
                       |- Init [&] pre [<->] px;
                       |- pre [&] Init [&] b [-->] F;
                       |- py [&] pre [&] close(F) [&] close(b) [-->] (substF ([(x, e)]) (rx));
                       |- py [-->] ry;
                       |- (l[=]Real 0) [-->] Gx;
                       |- (l[=]Real 0) [-->] Gy;
                       contain(Px,(ch ?? x))|]
              ==>   {px, py} (( (<F && b> :rg) [[> Px) || (ch !! e)) {rx, ry; Gx, Gy}"
apply (rule structSkipEL)
apply (rule structSkipELR)
apply (cut_tac H="l [=] Real 0" and Hx="l [=] Real 0" in CommunicationI2,auto)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule RL3a)
apply (simp add: True_def)
apply (rule impR)
apply (rule basic)
apply (rule Parallel2)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (rule Skip)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule LL3a)
apply (rule conjL)
apply (rule thinL)
apply (cut_tac P="l [=] Real 0 [-->] Gx" in cut,auto)
apply (rule thinL)
apply (rule thinR,auto)
apply (rule impL)
apply (rule basic)+
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule basic)
done

end