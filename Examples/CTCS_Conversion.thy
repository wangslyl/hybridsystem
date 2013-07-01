header {*An example on CTCS mode and level conversions.*}

theory CTCS_Conversion
  imports HHL
begin

(*First define the whole process, which is composed of a set of sub-processes.*)

type_synonym  segT = "exp * exp * exp * exp" (*Each segment contains v1, v2, s, and mode.*)
type_synonym  MAT = "segT list"

consts
MA_n :: "MAT"
t_delay :: real
minA :: real (*Min acceleration, CONSTANT*)
maxA :: real (*Max acc, CONSTANT*)

axioms 
assumpMinA: "minA > 0"
assumpMaxA: "maxA > 0"

(****************)
(* The variables*)
(****************)
(*Variable level*)
definition level :: "exp" where
"level == RVar ''le''"
 (*Displacement, variable s, the position of the train*)
definition sf :: "exp" where
"sf == RVar ''s''"
(*Variable x2*)
definition x2 :: "exp" where
"x2 == RVar ''x2''"
(*MA*)
definition seg1 :: "segT" where
"seg1 == (RVar ''v11'', RVar ''v12'', RVar ''x2'', String ''FS'')"
definition seg2 :: "segT" where
"seg2 == (RVar ''v21'', RVar ''v22'', RVar ''e2'', String ''CO'')"
definition MA :: "MAT" where
"MA == seg1#seg2#MA_n"
(*Temp_t0*)
definition Temp_t0 :: "exp" where
"Temp_t0 == RVar ''t0''" 
(*Temp_t1*)
definition Temp_t1 :: "exp" where
"Temp_t1 == RVar ''t1''" 
(*Temp_t2*)
definition Temp_t2 :: "exp" where
"Temp_t2 == RVar ''t2''" 
(*clock time*)
definition ct :: "exp" where
"ct == RVar ''ct''" 
 (*Velocity of the Train*)
definition vel :: "exp"
where "vel == RVar ''v''" 
 (*Acceleation of the Train*)
definition acc :: "exp" where
"acc == RVar ''a''"
(*Mode of train*)
definition md :: "exp" where
"md == SVar ''md''"
(*Variable b_rConf*)
definition br :: "exp" where
"br == BVar ''br''"

(****************)
(* The process RBC_lu*)
(****************)
consts
blua :: "string"  (*Variable b_lua*)
chlua :: "cname"
chlub :: "cname" (*Channel CH_LU*)
chlu1 :: "cname" (*Channel CH_LU*)
chlu2 :: "cname" (*Channel CH_LU*)
nx1 :: "string"
nx2 :: "string"

definition Plu :: "proc" where
"Plu ==  (IF ((BVar blua) [=] (Bool True)) 
      ((chlub !! (Bool True)) [[ (chlub !! (Bool False));(WTrue,DTrue);
      chlu1 !! (RVar nx1);(WTrue,DTrue);chlu2 !! (RVar nx2)))"

definition RBClu :: "proc" where
"RBClu ==  (Skip; (WTrue, l [[=]] Real 0); chlua ?? (BVar blua)); 
     (((BVar blua) [=] (Bool False)), DTrue); Plu"

lemma step_rbclu : "{BVar blua [=] (Bool False)} Plu {BVar blua [=] (Bool False); DTrue}"
apply (cut_tac p = "BVar blua [=] (Bool False)" and q = "BVar blua [=] (Bool False)" and 
               H = "DTrue" and 
               px = "BVar blua [=] (Bool False)" and qx = "BVar blua [=] (Bool False)" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Plu" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Plu_def)
apply (cut_tac p = "BVar blua [=] Bool False" and b = "(BVar blua [=] Bool True)" and 
               q = "BVar blua [=] Bool False" and G = "l [[=]] Real 0" in ConditionF,auto)
apply (rule impR)
apply (rule Trans1,auto)
apply fast+
apply (rule dimpR, rule basic)
apply (rule dimpR, simp add: DTrue_def, rule dimpR, rule basic)
done

(****************)
(* The driver process*)
(****************)
consts
chw :: "cname" (*Channel CH_win*)
chd :: "cname" (*Channel CH_DC*)
bw  :: "string"   (*Variable b_win*)

definition Pd :: "proc" where
"Pd ==  (IF ((BVar bw) [=] (Bool True)) 
      ((chd !! (Bool True)) [[ (chd !! (Bool False))))"

definition Driver :: "proc" where
"Driver ==  (Skip; (WTrue, l [[=]] Real 0); chw ?? (BVar bw)); 
     (((BVar bw) [=] (Bool False)), DTrue); Pd"

lemma step_driver : "{BVar bw [=] (Bool False)} Pd {BVar bw [=] (Bool False); DTrue}"
apply (cut_tac p = "BVar bw [=] (Bool False)" and q = "BVar bw [=] (Bool False)" and 
               H = "DTrue" and 
               px = "BVar bw [=] (Bool False)" and qx = "BVar bw [=] (Bool False)" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Pd" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Pd_def)
apply (cut_tac p = "BVar bw [=] Bool False" and b = "(BVar bw [=] Bool True)" and 
               P = "(chd!!(Bool True)[[chd!!(Bool False))" and
               q = "BVar bw [=] Bool False" and G = "l [[=]] Real 0" in ConditionF)
apply (rule impR)
apply (rule Trans1,auto)
apply fast+
apply (rule dimpR, rule basic)
apply (rule dimpR, simp add: DTrue_def, rule dimpR, rule basic)
done

(****************)
(* The process RBC_ma*)
(****************)
consts
brma :: "string"
chma3 :: "cname"
chorma :: "cname"
chrma :: "cname"
eoa3 :: "exp"
updatema3 :: "exp => exp"

definition Prma :: "proc" where
"Prma ==  (IF ((BVar brma) [=] (Bool True)) (chorma ?? eoa3; (WTrue,DTrue); chrma !! updatema3(eoa3)))"

definition RBCma :: "proc" where
"RBCma ==  (Skip; (WTrue, l [[=]] Real 0); chma3 ?? (BVar brma)); 
     (((BVar brma) [=] (Bool False)), DTrue); Prma"

lemma step_rbcma : "{BVar brma [=] (Bool False)} Prma {BVar brma [=] (Bool False); DTrue}"
apply (cut_tac p = "BVar brma [=] (Bool False)" and q = "BVar brma [=] (Bool False)" and 
               H = "DTrue" and 
               px = "BVar brma [=] (Bool False)" and qx = "BVar brma [=] (Bool False)" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Prma" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Prma_def)
apply (cut_tac p = "BVar brma [=] Bool False" and b = "(BVar brma [=] Bool True)" and 
               q = "BVar brma [=] Bool False" and G = "l [[=]] Real 0" in ConditionF,auto)
apply (rule impR)
apply (rule Trans1,auto)
apply fast+
apply (rule dimpR, rule basic)
apply (rule dimpR, simp add: DTrue_def, rule dimpR, rule basic)
done

(****************)
(* The process TCC_ma*)
(****************)
consts
btma :: "string"
chma2 :: "cname"
chotma :: "cname"
chtma :: "cname"
eoa2 :: "exp"
updatema2 :: "exp => exp"

definition Ptma :: "proc" where
"Ptma ==  (IF ((BVar btma) [=] (Bool True)) (chotma ?? eoa2; (WTrue,DTrue); chtma !! updatema2(eoa2)))"

definition TCC :: "proc" where
"TCC ==  (Skip; (WTrue, l [[=]] Real 0); chma2 ?? (BVar btma)); 
     (((BVar btma) [=] (Bool False)), DTrue); Ptma"

lemma step_tcc : "{BVar btma [=] (Bool False)} Ptma {BVar btma [=] (Bool False); DTrue}"
apply (cut_tac p = "BVar btma [=] (Bool False)" and q = "BVar btma [=] (Bool False)" and 
               H = "DTrue" and 
               px = "BVar btma [=] (Bool False)" and qx = "BVar btma [=] (Bool False)" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Ptma" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Ptma_def)
apply (cut_tac p = "BVar btma [=] Bool False" and b = "(BVar btma [=] Bool True)" and 
               q = "BVar btma [=] Bool False" and G = "l [[=]] Real 0" in ConditionF,auto)
apply (rule impR)
apply (rule Trans1,auto)
apply fast+
apply (rule dimpR, rule basic)
apply (rule dimpR, simp add: DTrue_def, rule dimpR, rule basic)
done

(****************)
(* The train process*)
(****************)

(*checkV1, checkV2: check the given speed is less than all v1 and v2 of MAT.*)
primrec checkV1 :: "MAT => exp => fform" where
"checkV1 ([], v) = WTrue" |
"checkV1 ((a # ma), v) = ((v [<] (fst (a))) [&] (checkV1 (ma, v)))"
primrec checkV2 :: "MAT => exp => fform" where
"checkV2 ([], v) = WTrue" |
"checkV2 ((a # ma), v) = ((v [<] (fst (snd (a)))) [&] (checkV2 (ma, v)))"

(*checkS: checks the given speed is less than all the dynamic curves of MAT.*)
primrec checkS :: "MAT => exp => exp => fform" where
"checkS ([], v, s) = WTrue" |
"checkS (a#ma, v, s) = ((((v[*]v)[+](((Real 2)[*](Real minA))[*]s)) [<] 
                   ( (((fst(a)))[*]((fst(a)))) [+] 
                   (((Real 2)[*](Real minA))[*]((fst (snd (snd (a))))))))
                   [&] (checkS ((ma), v, s)))" 

definition B0 :: "fform" where
"B0 == ((vel[>=] Real 0) [|] ((acc) [>=] Real 0) [|] (( ct) [<] (( Temp_t0) [+] (Real t_delay))))"

definition B1 :: "fform" where
"B1 == ( (checkV2 (MA, vel)) [|] ((acc) [<] Real 0) [|] (( ct) [<] (( Temp_t1) [+] (Real t_delay))))"

definition B2 :: "fform" where
"B2 ==  ((checkV1 (MA, vel)) [&] (checkS (MA, vel, sf))) [|]  (acc [=] Real (- (minA))) "

consts
isBalice :: "exp => fform"

definition B3 :: "fform" where
"B3 == (([~](level [=] (Real 2))) [|] ([~] isBalice(sf)))"

definition B4 :: "fform" where
"B4 == (([~](level [=] (Real 2.5))) [|] (sf [<=] x2))"

(*Use pre-defined function hd.*)
definition B5 :: "fform" where
"B5 == (md [=] (snd ( snd ( snd (hd(MA))))))"

definition B6 :: "fform" where
"B6 == (([~](level [=] (Real 3))) 
    [|] ([~] (String ''CO'' [=]  (snd ( snd ( snd (hd( tl (MA))))))))
    [|] (br [=] Bool True)
    [|] ((((fst (snd (snd (hd (MA))))) [-] sf) [>] Real 0) [&] 
           (((fst (snd (snd (hd (MA))))) [-] sf) [<] Real 300))
    [|] ((ct) [<] (Temp_t2 [+] Real t_delay)))"

definition B7 :: "fform" where
"B7 == (sf [<=] ((fst (snd (snd (seg1))))))"

definition B :: fform where
"B == (B1 [&] B2 [&] B3 [&] B4 [&] B5 [&] B6 [&] B7)"

(*Invariant for Train movement*)
definition inv :: fform where 
"inv == (checkS (MA, vel, sf))"

(*Precondition*)
definition Pre :: fform where
"Pre == (level [=] Real 2.5)
      [&] (((fst (snd (snd (seg1))))) [=] x2)
      [&] (((snd (snd (snd (seg1))))) [=] (String ''FS''))
      [&] (((snd (snd (snd (seg2))))) [=] (String ''CO''))
      [&] (((fst (seg1))) [=] Real 0)"
definition Init :: fform where
"Init == (x2 [-] sf [>] Real 300) [&] B1 [&] B2
      [&] (checkS (MA, vel, sf)) "

(*The following presents the proof of the example.*)

(*The continuous part*)
definition Move :: proc where
"Move == <inv && B> : (l [[>]] Real 0)"

(*P_train includes six sub-processes in sequence.*)
definition P1 :: proc where
"P1 == (IF B6 chw !! (Bool False)); (WTrue, DTrue); (IF ([~] B6) chw!! (Bool True))"

(*For this case, B6 is True.*)
(*Add {*assert B6*} before this process. This is proved in Assert1*)
definition SP1 :: proc where
"SP1 == chw !! (Bool False)"

definition SP2 :: proc where
"SP2 == chlua !! (Bool False)"

definition SP3 :: proc where
"SP3 == chma3 !! (Bool False)"

definition SP4 :: proc where
"SP4 == chma2 !! (Bool False)"

(*Variable c, used in Q12.*)
definition cv :: "exp" where
"cv == RVar ''cv''"
definition Q11 :: proc where
"Q11 == (IF ([~]B0) ( ((Temp_t0 := ct); (Pre [&] sf [<=] x2, l [[=]] (Real 0)); 
         NON R ''cv'' : (cv [>] Real 0 [&] (cv [<] Real maxA)) acc := cv) ))"

definition Q12 :: proc where
"Q12 == (IF ([~] B1) ((Temp_t1 := ct); (Pre [&] sf [<=] x2, l [[=]] (Real 0)); 
         NON R ''cv'' : ((cv [>] Real (-minA)) [&] (cv [<] Real maxA)) acc := (cv)) )"

definition Q13 :: proc where
"Q13 == (IF ([~] B2) acc := (Real (- minA)))"

definition Q2 :: proc where
"Q2 == (IF ([~] B3) level := (Real 3))"

consts x1 :: "exp"

definition Q3 :: proc where
"Q3 == (IF ([~] B4) ((chlub ?? (Bool False));(WTrue,DTrue);
      chlu1 ?? x1;(WTrue,DTrue);chlu2 !! x2;(WTrue,DTrue);level :=(Real 2.5)))"

definition Q4 :: proc where
"Q4 == (IF ([~] B5) ((md) := ((snd (snd (snd (hd (MA))))))))"

definition Q5 :: proc where
"Q5 == (IF ([~] B6) ((Temp_t2) := (ct); (WTrue, DTrue);chd ?? br; (WTrue, DTrue); 
       (IF (br [=] Bool True) ((fst (hd (tl (MA)))) := (Real 40)))))"

consts
geteoa :: "MAT => exp"
setma2 :: "exp => MAT => proc"
setma3 :: "exp => MAT => proc"
reoa2 :: "exp"
reoa3 :: "exp"

definition Q6 :: proc where
"Q6 == (IF ([~] B7) (chorma !! geteoa(MA);(WTrue,DTrue);chrma ?? reoa3;(WTrue,DTrue);
       setma3(reoa3,MA);(WTrue,DTrue);chotma !! geteoa(MA);(WTrue,DTrue);chrma ?? reoa2;
       (WTrue,DTrue);setma2(reoa2,MA)))"

definition Imd :: mid where
"Imd == (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))))"

definition Train :: proc where
"Train == ((((((((Move; Imd; Q11; Imd; Q12; Imd; Q13); Imd; SP2); Imd; 
          (Q2; Imd; Q3; Imd; Q4)); Imd; SP1); Imd;
          Q5); Imd; SP3); Imd; SP4); Imd; Q6)"
 
definition System :: proc where
"System == ((((Train)* || (RBClu)*) || (Driver)*) || (RBCma)*) || (TCC)*"

(***********************************************************)
(***********************************************************)
(* Process definition finished, proof part starts. *)
(***********************************************************)
(***********************************************************)

(*********************************)
(**for differential equation**)

lemma assist_cont_1 : "|- Init [-->] inv"
apply (simp add:Init_def inv_def)
apply (rule impR)
apply fast
done

lemma assist_cont_2_a: "[|s <= t; t < (u::real)|] ==> (s < u)"
apply (auto)
done

lemma assist_cont_2_b: "[|s <= t; s ~=u; t = (u::real)|] ==> (s < u)"
apply (auto)
done

lemma assist_cont_2_c: "2 * minA * rvar(''s'') <= rvar(''v'') * rvar(''v'') + 2 * minA * rvar(''s'')"
apply (auto)
done

lemma assist_cont_2: "close(checkS(MA, vel, sf)), Pre |- sf [<=] x2"
apply (unfold MA_def Pre_def,auto)
apply (rule conjL)+
apply (cut_tac P="vel [*] vel [+] (Real 2 [*] Real minA) [*] sf [<]
    fst(seg2) [*] fst(seg2) [+] (Real 2 [*] Real minA) [*] fst(snd(snd(seg2))) [|]
    vel [*] vel [+] (Real 2 [*] Real minA) [*] sf [=]
    fst(seg2) [*] fst(seg2) [+] (Real 2 [*] Real minA) [*] fst(snd(snd(seg2)))" in thinL,auto)
apply (cut_tac P="close(checkS(MA_n, vel, sf))" in thinL,auto)
apply (cut_tac P="level [=] Real 5 / 2" in thinL,auto)
apply (cut_tac P="fst(snd(snd(seg1))) [=] x2" in thinL,auto)
apply (cut_tac P="snd(snd(snd(seg1))) [=] String ''FS''" in thinL,auto)
apply (cut_tac P="snd(snd(snd(seg2))) [=] String ''CO''" in thinL,auto)
apply (unfold seg1_def seg2_def level_def x2_def sf_def vel_def equal_less_def)
apply (rule Trans2,auto)
apply (subgoal_tac "2 * minA * rvar(''s'') < 2 * minA * rvar(''x2'') & minA >0",auto)
apply (cut_tac s="2 * minA * rvar(''s'')"
    and t="rvar(''v'') * rvar(''v'') + 2 * minA * rvar(''s'')"
    and u="2 * minA * rvar(''x2'')" in assist_cont_2_a,auto)
apply (rule assumpMinA)
apply (subgoal_tac "2 * minA * rvar(''s'') < 2 * minA * rvar(''x2'')")
apply (subgoal_tac "minA >0", simp)
apply (rule assumpMinA)
apply (cut_tac s="2 * minA * rvar(''s'')"
    and t="rvar(''v'') * rvar(''v'') + 2 * minA * rvar(''s'')"
    and u="2*minA * rvar(''x2'')" in assist_cont_2_b)
apply (rule assist_cont_2_c, auto)
apply (subgoal_tac "minA >0", simp)
apply (rule assumpMinA)
done

lemma step_continuous: "{Pre [&] (sf [<=] x2)} Move {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))}"
apply (cut_tac b="inv" in Condition,auto)
(*1*)
apply (simp add:Move_def)
apply (cut_tac Init = "inv" and p = "Pre" and F = "inv" and b = "B" and 
               Rg = "(l [[>]] Real 0)" and q = "Pre [&] sf [<=] x2" and 
               G = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" in ContinueY,auto)
apply (rule conjR)
apply fast
apply (rule impR)
apply (rule conjR)
apply fast
apply (rule conjL)+
apply (cut_tac P="NotForm(B)" in thinL,auto)
apply (simp add: inv_def)
apply (rule exchL)
apply (rule assist_cont_2)
apply (rule dimpR)
apply (rule dconjL)
apply (rule ddisjL)
apply (rule ddisjR,rule basic)
apply (rule exchL)
apply (rule thinL)
apply (rule ddisjR)
apply (rule thinR)
apply (cut_tac s = "close(inv) [&] Pre [&] close(B)" and t= "Pre [&] sf [<=] x2" in DC18,auto)
apply (rule conjL)+
apply (rule conjR)
apply fast
apply (cut_tac P="close(B)" in thinL,auto)
apply (simp add:inv_def)
apply (rule assist_cont_2)
apply (rule ConsequenceS,auto)
apply fast
apply (rule dimpR, rule basic)
(*2*)
apply (simp add:Move_def)
apply (cut_tac Init="sf [<=] x2 [&] [~]inv" and p=Pre and F = "inv" and b = "B" and 
               Rg = "(l [[>]] Real 0)" and q = "Pre [&] sf [<=] x2" and 
               G = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" in ContinueN)
apply fast
apply (rule dimpR, rule ddisjR, rule basic)
apply (rule ConsequenceS,auto)
apply fast
apply (rule dimpR, rule basic)
done


(**********************************)
(**for Q11****)

lemma assist_Q11_1_a : "substF([(Temp_t0, ct)], Pre) = Pre"
apply (simp add: Temp_t0_def ct_def Pre_def seg1_def)
apply (simp add: level_def x2_def seg2_def)
done

lemma assist_Q11_1_b : "substF([(Temp_t0, ct)], sf [<=] x2) = (sf [<=] x2)"
apply (simp add: Temp_t0_def ct_def equal_less_def)
apply (simp add: sf_def x2_def)
done

lemma assist_Q11_1 : "{Pre [&] sf [<=] x2}(Temp_t0) := (ct) {Pre [&] sf [<=] x2; l [[=]] Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "Temp_t0" and 
               f = "ct" and q = "Pre [&] sf [<=] x2" and 
               G = "l [[=]] Real 0" in Assign,auto)
prefer 3
apply (rule impR)
apply (rule conjR)
apply (simp add: assist_Q11_1_a)
apply fast
apply (simp add: assist_Q11_1_b)
apply fast
apply (unfold Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def,auto)
apply (rule dimpR, rule basic)
done


lemma assist_Q11_2_a : "substF([(acc, cv)], Pre) = Pre"
apply (simp add:acc_def cv_def Pre_def)
apply (simp add:level_def x2_def seg1_def seg2_def)
done

lemma assist_Q11_2_b : "substF([(acc, cv)], sf [<=] x2) = (sf [<=] x2)"
apply (simp add:acc_def cv_def equal_less_def)
apply (simp add:sf_def x2_def)
done

lemma assist_Q11_2 : "{Pre [&] sf [<=] x2} acc := (cv){Pre [&] sf [<=] x2; l [[=]] Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "acc" and 
               f = "cv" and q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in Assign,auto)
prefer 3
apply (simp add: assist_Q11_2_a assist_Q11_2_b)
apply fast
apply (unfold Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def,auto)
apply (rule dimpR, rule basic)
done

lemma assist_Q11_3 : "{Pre [&] sf [<=] x2} NON R ''cv'': (cv [>] Real 0 [&] cv [<]  Real maxA) 
       CTCS_Conversion.acc := cv{Pre [&] sf [<=] x2;l [[=]] Real 0}"
apply (cut_tac p = "Pre [&] sf [<=] x2" and q = "Pre [&] sf [<=] x2" and 
               G = "l [[=]] Real 0" and b = "cv [>] Real 0 [&] cv [<]  Real maxA"and 
               P = "acc := (cv)" in Nondeterministic,auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] cv [>] Real 0 [&] cv [<] Real maxA" and
               q = "Pre [&] sf [<=] x2" and H= "l [[=]] Real 0" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "l [[=]] Real 0" and P = "acc := (cv)" in ConsequenceS, auto)
apply (rule assist_Q11_2)
apply fast
apply (rule dimpR, rule basic)
done

lemma step_Q11 : "{Pre [&] sf [<=] x2} Q11 {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))} "
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Q11" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q11_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B0" and P = "IF ([~] B0) (Temp_t0 := ct; 
        (Pre [&] sf [<=] x2, l [[=]] Real 0) ; NON R ''cv'' : (cv [>]
        Real 0 [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv)" and
        q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in Condition, auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B0" and b = "[~] B0"
           and P = "(Temp_t0 := ct; (Pre [&] sf [<=] x2, l [[=]] Real 0);
             NON R ''cv'' : (cv [>] Real 0 [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv)"
           and q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionT, auto)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B0" and q = "Pre [&] sf [<=] x2" and 
               H = "l [[=]] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [[=]] Real 0" and 
               P = "Temp_t0 := ct; (Pre [&] sf [<=] x2, l [[=]] Real 0) ; 
                NON R ''cv'' : (cv [>] Real 0 [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv" 
                in ConsequenceS, auto)
apply (cut_tac P = "(Temp_t0) := (ct)" and Q = "NON R ''cv'' : (cv [>] Real 0 [&] cv [<] Real maxA) 
                 acc := (cv)" and p = "Pre [&] sf [<=] x2" and m = "Pre [&] sf [<=] x2" and
               H = "l [[=]] Real 0" and q = "Pre [&] sf [<=] x2" and 
               G = "l [[=]] Real 0" in Sequence )
apply (rule assist_Q11_1)
apply (rule assist_Q11_3)
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "l [[=]] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [[=]] Real 0 [^] l [[=]] Real 0" and 
               P = "Temp_t0 := ct; (Pre [&] sf [<=] x2, l [[=]] Real 0) ; 
                NON R ''cv'' : (cv [>] Real 0 [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv" 
                in ConsequenceS, auto)
apply fast
apply (rule dimpR)
apply (rule LL4)
apply (rule basic)
apply fast
apply (rule dimpR, rule basic)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] [~] B0" and b = "[~] B0"
           and P = "((Temp_t0) := (ct); (Pre [&] sf [<=] x2,l [[=]] Real 0) ; 
                NON R ''cv'' : (cv [>] Real 0 [&] cv [<] Real maxA) acc := (cv))"
           and q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionF, auto)
apply fast+
apply (rule dimpR, rule basic)
apply (rule dimpR, rule ddisjR, rule basic)
done

(*************************************)
(*for Q12*)

lemma assist_Q12_1_a : "substF([(Temp_t1, ct)], Pre) = Pre"
apply (simp add: Temp_t1_def ct_def Pre_def seg1_def)
apply (simp add: level_def x2_def seg2_def)
done

lemma assist_Q12_1_b : "substF([(Temp_t1, ct)], sf [<=] x2) = (sf [<=] x2)"
apply (simp add: Temp_t1_def ct_def equal_less_def)
apply (simp add: sf_def x2_def)
done

lemma assist_Q12_1 : "{Pre [&] sf [<=] x2}(Temp_t1) := (ct) {Pre [&] sf [<=] x2; l [[=]] Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "Temp_t1" and 
               f = "ct" and q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in Assign,auto)
prefer 3
apply (rule impR)
apply (simp add: assist_Q12_1_a assist_Q12_1_b)
apply fast+
apply (unfold Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def,auto)
apply (rule dimpR, rule basic)
done

lemma assist_Q12_2 : "{Pre [&] sf [<=] x2} NON R ''cv'': (cv [>] Real - minA [&] cv [<] Real maxA) acc := (cv){Pre [&] sf [<=] x2;l [[=]] Real 0}"
apply (cut_tac p = "Pre [&] sf [<=] x2" and q = "Pre [&] sf [<=] x2" and 
               G = "l [[=]] Real 0" and b = "cv [>] Real - minA [&] cv [<] Real maxA" and
               P = "acc := (cv)" in Nondeterministic,auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] cv [>] Real - minA [&] cv [<] Real maxA" and
               q = "Pre [&] sf [<=] x2" and H= "l [[=]] Real 0" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "l [[=]] Real 0" and P = "acc := (cv)" in ConsequenceS, auto)
apply (rule assist_Q11_2)
apply fast
apply (rule dimpR, rule basic)
done

lemma step_Q12 : "{Pre [&] sf [<=] x2} Q12 {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))} "
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Q12" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q12_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B1" and P = "IF ([~] B1) ((Temp_t1) := (ct); 
                 (Pre [&] sf [<=] x2, l [[=]] Real 0) ; NON R ''cv'': (cv [>] Real - minA [&] 
                 cv [<] Real maxA) acc := cv)" and q = "Pre [&] sf [<=] x2" and 
               G = "l [[=]] Real 0" in Condition, auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B1" and b = "[~] B1" and
               P = "((Temp_t1) := (ct); (Pre [&] sf [<=] x2,l [[=]] Real 0);
                 NON R ''cv'': (cv [>] Real - minA [&] cv [<] Real maxA) acc := (cv))"
           and q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionT, auto)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B1" and q = "Pre [&] sf [<=] x2" and 
               H= "l [[=]] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [[=]] Real 0" and
               P = "(Temp_t1) := (ct); (Pre [&] sf [<=] x2,l [[=]] Real 0); 
                 NON R ''cv'': (cv [>] Real - minA [&] cv [<] Real maxA) acc := (cv)" 
                 in ConsequenceS, auto)
apply (cut_tac P = "(Temp_t1) := (ct)" and Q = "NON R ''cv'': (cv [>] Real - minA [&] 
                 cv [<] Real maxA) acc := (cv)" and p = "Pre [&] sf [<=] x2" and 
               m = "Pre [&] sf [<=] x2" and H = "l [[=]] Real 0" and
               q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in Sequence )
apply (rule assist_Q12_1)
apply (rule assist_Q12_2)
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "l [[=]] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [[=]] Real 0 [^] l [[=]] Real 0" and 
               P = "Temp_t1 := ct; (Pre [&] sf [<=] x2, l [[=]] Real 0) ; 
                NON R ''cv'' : (cv [>] Real - minA [&] (cv [<] Real maxA)) CTCS_Conversion.acc := cv" 
                in ConsequenceS, auto)
apply (rule conjR)
apply (rule impR)
apply (rule basic)
apply (rule impR)
apply (rule basic)
apply (rule dimpR, rule LL4, rule basic)
apply fast
apply (rule dimpR, rule basic)
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] [~] B1" and b = "[~] B1" and
               P = "((Temp_t1) := (ct); (Pre [&] sf [<=] x2,l [[=]] Real 0);
                 NON R ''cv'': (cv [>] Real - minA [&] cv [<] Real maxA) acc := (cv))" and
               q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionF, auto)
apply fast+
apply (rule dimpR, rule basic)
apply (rule dimpR, rule ddisjR, rule basic)
done

(**********************************)
(**for Q13****)

lemma assist_Q13_1_a : "substF([(acc, Real - minA)], Pre) = Pre"
apply (simp add:acc_def Pre_def)
apply (simp add:level_def x2_def seg1_def seg2_def)
done

lemma assist_Q13_1_b : "substF([(acc, Real - minA)], sf [<=] x2) = (sf [<=] x2)"
apply (simp add:acc_def equal_less_def)
apply (simp add:sf_def x2_def)
done


lemma assist_Q13_1 : " {(Pre [&] sf [<=] x2)} acc := (Real - minA) {Pre [&] sf [<=] x2;l [[=]] Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "acc" and 
               f = "(Real - minA)" and q = "Pre [&] sf [<=] x2" and 
               G = "l [[=]] Real 0" in Assign)
apply (simp add: Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def)
apply (simp add: assist_Q13_1_a assist_Q13_1_b)
apply fast
apply (rule dimpR, rule basic)
apply assumption
done

lemma step_Q13 : "{Pre [&] sf [<=] x2} Q13 {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))} "
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Q13" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q13_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B2" and P = "IF ([~] B2) (acc := (Real - minA))" and
               q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in Condition, auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2)  [&] [~] B2" and b = "[~] B2" and 
               P = "acc := (Real - minA)" and q = "Pre [&] sf [<=] x2" and 
               G = "l [[=]] Real 0" in ConditionT, auto)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B2" and q = "Pre [&] sf [<=] x2" and 
               H= "l [[=]] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [[=]] Real 0" and
               P = "acc := (Real - minA)" in ConsequenceS, auto)
apply (rule assist_Q13_1)
apply fast
apply (rule dimpR, rule basic)
apply (cut_tac p = "(Pre [&] sf [<=] x2)  [&] [~] [~] B2" and b = "[~] B2" and 
               P = "acc := (Real - minA)" and
               q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionF,auto)
apply fast+
apply (rule dimpR, rule basic)
apply (rule dimpR, rule ddisjR, rule basic)
done

(**********************)
(* for Q2 *)

lemma assist_Q2 : "|- Pre [&] sf [<=] x2 [-->] [~] [~] B3"
apply (simp add:Pre_def B3_def)
apply (rule impR)
apply (rule notR)
apply (rule notL)
apply (rule disjR)
apply (cut_tac P="[~] isBalice(sf)" in thinR,auto)
apply (rule Trans1)
apply (simp add: level_def)
done

lemma step_Q2 : "{Pre [&] sf [<=] x2} Q2 {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Q2" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q2_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B3"
           and q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionF,auto)
apply (rule assist_Q2)
apply (fast)+
apply (rule dimpR, rule basic)
apply (rule dimpR, rule ddisjR, rule basic)
done

(**********************)
(* for Q3 *)

lemma assist_Q3 : "|- Pre [&] sf [<=] x2 [-->] [~] [~] B4"
apply (simp add:Pre_def B4_def)
apply (rule impR)
apply (rule notR)
apply (rule notL)
apply (rule disjR)
apply (rule thinR)
apply fast
done

lemma step_Q3 : "{Pre [&] sf [<=] x2} Q3 {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Q3" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q3_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B4"
           and q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionF,auto)
apply (rule assist_Q3)
apply (fast)+
apply (rule dimpR, rule basic)
apply (rule dimpR, rule ddisjR, rule basic)
done

(**************)
(** for Q4**)

lemma assist_Q4_a : "(substF([(md, snd(snd(snd(hd(MA)))))], Pre)) = (Pre)"
apply (unfold Pre_def md_def)
apply (unfold level_def x2_def MA_def seg1_def seg2_def, auto)
done

lemma assist_Q4_b : "substF([(md, snd(snd(snd(hd(MA)))))], sf [<=] x2) = (sf [<=] x2)"
apply (unfold md_def equal_less_def)
apply (unfold sf_def x2_def MA_def, auto)
done

lemma assist_Q4 : "{(Pre [&] sf [<=] x2)} md := (snd(snd(snd(hd(MA)))))
                     {Pre [&] sf [<=] x2;l [[=]] Real 0}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and e = "md" and 
               f = "snd(snd(snd(hd(MA))))" and q = "Pre [&] sf [<=] x2" and 
               G = "l [[=]] Real 0" in Assign)
apply (simp add: Pre_def sf_def x2_def equal_less_def inPairForm_def inPairL_def inPairR_def inExp_def)
apply (rule impR)
apply (simp add: assist_Q4_a assist_Q4_b)
apply fast+
apply (rule dimpR, rule basic)
apply assumption
done

lemma step_Q4 : "{Pre [&] sf [<=] x2} Q4 {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Q4" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q4_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B5" and 
               P = "IF ([~] B5) (md := (snd(snd(snd(hd(MA))))))" and q = "Pre [&] sf [<=] x2" and 
               G = "l [[=]] Real 0" in Condition, auto)
apply (cut_tac p = "(Pre [&] sf [<=] x2)  [&] [~] B5" and b = "[~] B5" and 
               P = "(md) := (snd(snd(snd(hd(MA)))))" and
               q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionT, auto)
apply fast
apply (cut_tac p = "(Pre [&] sf [<=] x2) [&] [~] B5" and q = "Pre [&] sf [<=] x2" and 
               H= "l [[=]] Real 0" and px = "(Pre [&] sf [<=] x2)" and 
               qx = "Pre [&] sf [<=] x2" and Hx = "l [[=]] Real 0" and
               P = "md := (snd(snd(snd (hd(MA)))))" in ConsequenceS, auto)
apply (rule assist_Q4)
apply fast
apply (rule dimpR, rule basic)
apply (cut_tac p = "(Pre [&] sf [<=] x2)  [&] [~] [~] B5" and b = "[~] B5" and 
               P = "(md) := (snd(snd(snd(hd(MA)))))" and
               q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionF,auto)
apply fast+
apply (rule dimpR, rule basic)
apply (rule dimpR, rule ddisjR, rule basic)
done

(**************)
(** for Q5**)

lemma assist_Q5 : "|- Pre [&] sf [<=] x2 [-->] [~] [~] B6"
apply (rule impR)
apply (rule notR)
apply (rule notL)
apply (simp add:Pre_def B6_def level_def)
apply (rule disjR)
apply (rule exchR)
apply (rule thinR)
apply (rule conjL)
apply (rule exchL)
apply (rule conjL)
apply (rule thinL)
apply (rule exchL)
apply (rule thinL)
apply (rule Trans1,auto)
done

lemma step_Q5 : "{Pre [&] sf [<=] x2} Q5 {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))} "
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Q5" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q5_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B6" and 
               P = "((Temp_t2) := (ct); (WTrue, DTrue) ; chd??br; (WTrue,
                       DTrue) ; IF (br [=] Bool True) (fst(hd(tl(MA)))) := (Real 40))"
           and q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionF,auto)
apply (rule assist_Q5)
apply fast+
apply (rule dimpR, rule basic)
apply (rule dimpR, rule ddisjR, rule basic)
done

(**********************)
(* for Q6 *)

lemma assist_Q6 : "|- Pre [&] sf [<=] x2 [-->] [~] [~] B7"
apply (simp add:Pre_def B7_def)
apply (rule impR)
apply (rule notR)
apply (rule notL)
apply (cut_tac P="fst(snd(snd(seg1))) [=] x2 [&] sf [<=] x2" in cut,auto)
apply (rule conjL)+
apply (rule conjR)
apply (rule basic)+
apply (rule thinL)
apply (rule Trans1)
apply (simp add: sf_def seg1_def x2_def equal_less_def)
done

lemma step_Q6 : "{Pre [&] sf [<=] x2} Q6 {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))}"
apply (cut_tac p = "(Pre [&] sf [<=] x2)" and q = "Pre [&] sf [<=] x2" and 
               H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               px = "(Pre [&] sf [<=] x2)" and qx = "Pre [&] sf [<=] x2" and 
               Hx = "(l [[=]] Real 0)" and 
               P = "Q6" in ConsequenceS, auto)
prefer 2
apply (fast)
apply (simp add:Q6_def)
apply (cut_tac p = "Pre [&] sf [<=] x2" and b = "[~] B7"
           and q = "Pre [&] sf [<=] x2" and G = "l [[=]] Real 0" in ConditionF,auto)
apply (rule assist_Q6)
apply (fast)+
apply (rule dimpR, rule basic)
apply (rule dimpR, rule ddisjR, rule basic)
done

(************************)
(** composition**)

lemma DCR3_assist: "(high D) [^] (high D) |- (high D) [^] (high D),$E ==> (high D) [^] (high D) |- (high D),$E"
apply (rule DCR3)
apply fast
done

lemma step_part1_comp_assist: "|- ((l [[=]] Real 0) [[|]] high(Pre [&] sf [<=] x2)) [^]
                      ((l [[=]] Real 0) [[|]] high(Pre [&] sf [<=] x2))
                    [[-->]] (l [[=]] Real 0) [[|]] high(Pre [&] sf [<=] x2)"
apply (rule dimpR)
apply (rule LT1)
apply (rule LT1a)
apply (rule LL4)
apply (rule ddisjR)
apply fast
apply (rule LL3a)
apply (rule ddisjR)
apply fast
apply (rule LT1a)
apply (rule LL4)
apply (rule ddisjR)
apply fast
apply (rule ddisjR)
apply (rule thinR)
apply (cut_tac D="(Pre [&] sf [<=] x2)" in DCR3_assist,auto)
apply fast
done

lemma step_part1_comp : "{Pre [&] (sf [<=] x2)} (Move; Imd; Q11; Imd; Q12; Imd; Q13)
        {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))}"
(*Move*)
apply (cut_tac p = "Pre [&] (sf [<=] x2)" and P = "Move" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q11; Imd; Q12; Imd; Q13" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" in Sequence)
prefer 3
apply (simp add: Imd_def)
apply (rule ConsequenceS,auto)
apply (fast)
apply (rule step_part1_comp_assist)
apply (rule step_continuous)
(*Q11*)
apply (cut_tac p = "Pre [&] sf [<=] x2" and P = "Q11" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q12; Imd ; Q13" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" in Sequence)
prefer 3
apply (simp add: Imd_def)
apply (rule ConsequenceS,auto)
apply (fast)
apply (rule step_part1_comp_assist)
apply (rule step_Q11)
(*Q12,Q13*)
apply (cut_tac p = "Pre [&] sf [<=] x2" and P = "Q12" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q13" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" in Sequence)
prefer 3
apply (simp add: Imd_def)
apply (rule ConsequenceS,auto)
apply (fast)
apply (rule step_part1_comp_assist)
apply (rule step_Q12)
apply (rule step_Q13)
done

lemma step_part2_comp : "{Pre [&] sf [<=] x2} Q2; Imd; Q3; Imd; Q4
        {Pre [&] sf [<=] x2; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))}"
(*Q2*)
apply (cut_tac p = "Pre [&] sf [<=] x2" and P = "Q2" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q3; Imd; Q4" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" in Sequence)
prefer 3
apply (simp add: Imd_def)
apply (rule ConsequenceS,auto)
apply (fast)
apply (rule step_part1_comp_assist)
apply (rule step_Q2)
(*Q3,Q4*)
apply (cut_tac p = "Pre [&] sf [<=] x2" and P = "Q3" and
        m = "Pre [&] sf [<=] x2" and 
        H = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and
        Q = "Q4" and q = "Pre [&] sf [<=] x2" and 
        G = "(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" in Sequence)
prefer 3
apply (simp add: Imd_def)
apply (rule ConsequenceS,auto)
apply (fast)
apply (rule step_part1_comp_assist)
apply (rule step_Q3)
apply (rule step_Q4)
done

(*********************************)
(**with the communication**)

(*Assert holds.*)
lemma Assert1 : "(Pre [&] sf [<=] x2)|- B6"
apply (rule conjL)
apply (rule exchL)
apply (rule thinL)
apply (simp add:Pre_def B6_def seg1_def level_def x2_def)
apply (rule conjL)
apply (rule exchL)
apply (rule thinL)
apply (rule disjR)
apply (rule exchR)
apply (rule thinR)
apply (rule Trans1,auto)
done

(*********************************)
(*System proof*)
(*********************************)
lemma assist_System_proof : "|- (l [[=]] Real 0 [[|]] high (p)) [^] (l [[=]] Real 0 [[|]] high (p)) [[-->]] (l [[=]] Real 0 [[|]] high (p))"
apply (rule dimpR)
apply (rule LT1)
apply (rule LT1a)
apply (rule LL4)
apply (rule ddisjR, rule basic)
apply (rule LL3a)
apply (rule ddisjR, rule basic)
apply (rule LT1a)
apply (rule LL4)
apply (rule ddisjR, rule basic)
apply (rule ddisjR)
apply (rule thinR)
apply (cut_tac S = "p" in DCL3,auto)
apply (rule basic)
done

lemma dtrue_chop : "|- DTrue [^] DTrue [[-->]] DTrue"
apply (rule dimpR)
apply (simp add: DTrue_def)
apply (rule dimpR, rule basic)
done

(* All the fact* are create to support the steps, and all the 10 steps fforms the proof.*)
lemma System_proof : "{Init [&] Pre,WTrue,WTrue,WTrue,WTrue} System {Pre [&] sf [<=] x2, 
       WTrue,WTrue,WTrue,WTrue; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))), 
       DTrue,DTrue,DTrue,DTrue}"
(*eliminate Init by consequence*)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue,WTrue,WTrue,WTrue} System {Pre [&] sf [<=] x2, 
       WTrue,WTrue,WTrue,WTrue; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))), 
       DTrue,DTrue,DTrue,DTrue}")
apply (rule ConsequenceP5,auto)
apply (simp add:System_def)
apply (rule Trans)
apply (simp add: Init_def Pre_def sf_def x2_def equal_less_def)
apply (fast)
apply (rule dconjR)
apply (rule dimpR,rule basic)
apply (rule dconjR)
apply (rule dimpR,rule basic)
apply (rule dconjR)
apply (rule dimpR,rule basic)
apply (rule dconjR)
apply (rule dimpR,rule basic)
apply (rule dimpR,rule basic)
(*Repetition*)
apply (unfold System_def)
apply (rule Repetition5)
defer
apply (rule assist_System_proof)
apply (rule dtrue_chop)+
(*TCC*)
apply (unfold TCC_def)
apply (cut_tac Hx="DTrue" in Parallel15,auto)
defer
apply (subgoal_tac "{BVar btma [=] (Bool False)} Ptma {BVar btma [=] (Bool False); DTrue}")
apply (rule ConsequenceS,auto)
apply fast
apply (rule dimpR,rule basic)
apply (rule step_tcc)
apply (rule dtrue_chop)
apply (unfold Train_def)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue,WTrue,WTrue,WTrue} ((( ((((((((Move; Imd; Q11; Imd; Q12; Imd; Q13); Imd; SP2); Imd; (Q2; Imd; Q3; Imd; Q4)); Imd; SP1); Imd; Q5); Imd; SP3); Imd; SP4); (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))); Q6)||RBClu)||Driver)||RBCma)||(Skip;(WTrue,l [[=]] Real 0);chma2??(BVar btma)) {Pre [&] sf [<=] x2, WTrue,WTrue,WTrue,(BVar btma [=] Bool False); (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))), DTrue,DTrue,DTrue,DTrue}")
apply (simp add: Imd_def)
apply (cut_tac Hx="(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" in Parallel115,auto)
defer
apply (rule step_Q6)
apply (rule assist_System_proof)
apply (unfold SP4_def)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue,WTrue,WTrue,WTrue} (( ((((((((Move; Imd; Q11; Imd; Q12; Imd; Q13); Imd; SP2); Imd; (Q2; Imd; Q3; Imd; Q4)); Imd; SP1); Imd; Q5); Imd; SP3); (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))); chma2!!(Bool False))||RBClu)||Driver)||RBCma)||(Skip;(WTrue,l [[=]] Real 0);chma2??(BVar btma)) {Pre [&] sf [<=] x2, WTrue,WTrue,WTrue,(BVar btma [=] Bool False); (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))), DTrue,DTrue,DTrue,DTrue}")
apply (simp add: Imd_def)
apply (cut_tac H="DTrue" and Hx="(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               Hy="DTrue" in Communication5,auto)
defer
apply fast
apply (rule dconjR)
apply (rule dimpR)
apply (rule LT1)
apply (rule LL3a)
apply (rule ddisjR, rule basic)
apply (rule DCL3)
apply (rule ddisjR, rule basic)
apply (rule dimpR, simp add: DTrue_def, rule dimpR, rule basic)+
apply (rule dimpR, rule dconjL, rule basic)+
apply (rule Parallel25)
defer
apply (rule Skip, rule dimpR, rule basic)
(*RBCma*)
apply (unfold RBCma_def)
apply (cut_tac Hx="DTrue" in Parallel14,auto)
defer
apply (subgoal_tac "{BVar brma [=] (Bool False)} Prma {BVar brma [=] (Bool False); DTrue}")
apply (rule ConsequenceS,auto)
apply fast
apply (rule dimpR,rule basic)
apply (rule step_rbcma)
apply (rule dtrue_chop)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue,WTrue,WTrue} ((( (((((Move; Imd; Q11; Imd; Q12; Imd; Q13); Imd; SP2); Imd; (Q2; Imd; Q3; Imd; Q4)); Imd; SP1); Imd; Q5); (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))); SP3)||RBClu)||Driver)||(Skip; (WTrue, l [[=]] Real 0); chma3??(BVar brma)) {Pre [&] sf [<=] x2, WTrue,WTrue,(BVar brma [=] Bool False); (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))), DTrue,DTrue,DTrue}")
apply (simp add: Imd_def)
apply (unfold SP3_def)
apply (cut_tac H="DTrue" and Hx="(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               Hy="DTrue" in Communication4,auto)
defer
apply fast
apply (rule dconjR)
apply (rule dimpR)
apply (rule LT1)
apply (rule LL3a)
apply (rule ddisjR, rule basic)
apply (rule DCL3)
apply (rule ddisjR, rule basic)
apply (rule dimpR, simp add: DTrue_def, rule dimpR, rule basic)+
apply (rule dimpR, rule dconjL, rule basic)+
apply (rule Parallel24)
defer
apply (rule Skip, rule dimpR, rule basic)
(*Driver*)
apply (unfold Driver_def)
apply (cut_tac Hx="DTrue" in Parallel13,auto)
defer
apply (subgoal_tac "{BVar bw [=] (Bool False)} Pd {BVar bw [=] (Bool False); DTrue}")
apply (rule ConsequenceS,auto)
apply fast
apply (rule dimpR,rule basic)
apply (rule step_driver)
apply (rule dtrue_chop)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue,WTrue} ( (((((Move; Imd; Q11; Imd; Q12; Imd; Q13); Imd; SP2); Imd; (Q2; Imd; Q3; Imd; Q4)); Imd; SP1); (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))); Q5)||RBClu)||(Skip; (WTrue, l [[=]] Real 0); chw ?? (BVar bw)) {Pre [&] sf [<=] x2, WTrue,(BVar bw [=] Bool False); (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))), DTrue,DTrue}")
apply (simp add: Imd_def)
apply (cut_tac Hx="(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" in Parallel113,auto)
defer
apply (rule step_Q5)
apply (rule assist_System_proof)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue,WTrue} ( ((((Move; Imd; Q11; Imd; Q12; Imd; Q13); Imd; SP2); Imd; (Q2; Imd; Q3; Imd; Q4)); (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))); SP1)||RBClu)||(Skip; (WTrue, l [[=]] Real 0); chw ?? (BVar bw)) {Pre [&] sf [<=] x2, WTrue,(BVar bw [=] Bool False); (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))), DTrue,DTrue}")
apply (simp add: Imd_def)
apply (unfold SP1_def)
apply (cut_tac H="DTrue" and Hx="(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               Hy="DTrue" in Communication3,auto)
defer
apply fast
apply (rule dconjR)
apply (rule dimpR)
apply (rule LT1)
apply (rule LL3a)
apply (rule ddisjR, rule basic)
apply (rule DCL3)
apply (rule ddisjR, rule basic)
apply (rule dimpR, simp add: DTrue_def, rule dimpR, rule basic)+
apply (rule dimpR, rule dconjL, rule basic)+
apply (rule Parallel23)
defer
apply (rule Skip, rule dimpR, rule basic)
(*RBClu*)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue} ( ((((Move; Imd; Q11; Imd; Q12; Imd; Q13); Imd; SP2); (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))); (Q2; Imd; Q3; Imd; Q4)))||RBClu) {Pre [&] sf [<=] x2, WTrue; (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))), DTrue}")
apply (simp add: Imd_def)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue} ( ((((Move; Imd; Q11; Imd; Q12; Imd; Q13); Imd; SP2); (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))); (Q2; Imd; Q3; Imd; Q4)))||RBClu) {Pre [&] sf [<=] x2, WTrue; (((l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))) [^] ((l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))))), DTrue [^] DTrue}")
apply (rule ConsequenceP,auto)
apply fast
apply (rule dconjR)
apply (rule assist_System_proof)
apply (rule dtrue_chop)
apply (unfold RBClu_def)
apply (rule Parallel1)
defer
apply (rule step_part2_comp)
apply (subgoal_tac "{BVar blua [=] (Bool False)} Plu {BVar blua [=] (Bool False); DTrue}")
apply (rule ConsequenceS,auto)
apply fast
apply (rule dimpR,rule basic)
apply (rule step_rbclu)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue} ( ((Move; Imd; Q11; Imd; Q12; Imd; Q13); (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))); SP2)||((Skip; (WTrue, l [[=]] Real 0); chlua ?? (BVar blua)))) {Pre [&] sf [<=] x2,(BVar blua [=] Bool False); (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))), DTrue}")
apply (simp add: Imd_def)
apply (unfold SP2_def)
apply (subgoal_tac "{Pre [&] sf [<=] x2,WTrue} ( ((Move; Imd; Q11; Imd; Q12; Imd; Q13); (Pre [&] sf [<=] x2, (l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))); chlua!!(Bool False))||((Skip; (WTrue, l [[=]] Real 0); chlua ?? (BVar blua)))) {Pre [&] sf [<=] x2,(BVar blua [=] Bool False); ((l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2))))[[&]]DTrue, DTrue[[&]]DTrue}")
apply (rule ConsequenceP,auto)
apply fast
apply (rule dconjR)
apply (rule dimpR, rule dconjL, rule basic)+
apply (cut_tac H="DTrue" and Hx="(l [[=]] Real 0) [[|]] (high (Pre [&] (sf [<=] x2)))" and 
               Hy="l [[=]] Real 0" in Communication,auto)
defer
apply fast
apply (rule dconjR)
apply (rule dimpR)
apply (rule LT1)
apply (rule LL3a)
apply (rule ddisjR, rule basic)
apply (rule DCL3)
apply (rule ddisjR, rule basic)
apply (rule dimpR, simp add: DTrue_def, rule dimpR, rule basic)+
apply (rule Parallel2)
apply (rule step_part1_comp)
apply (rule Skip, rule dimpR, rule basic)
done

end