(* This file requires:

 - An Isabelle Snapshot from no earlier than October 5, 2007

*)

(*
   This contains occurence typing with:
   - variables as tests
   - eta-expansion
*)

theory TypedSchemePreOr
imports Nominal

begin

ML {*ResAtp.set_prover "vampire"*}
(* ML {* ThmDeps.enable() *} *) 


(* datatype definitions *)
atom_decl name


datatype ty =
    Top | Int | TT | FF | Arr "ty" "ty" "latent_eff" ("_ \<rightarrow> _ : _" [100,100] 100) | Union "ty list"  
and latent_eff = NE | Latent ty

constdefs
"BoolTy == Union [TT , FF]"

primrec (unchecked perm_ty)
 "pi\<bullet>(ty.Top) = ty.Top"
 "pi\<bullet>(ty.Int) = ty.Int"
 "pi\<bullet>(TT) = TT"
 "pi\<bullet>(FF) = FF"
 "pi\<bullet>(\<tau> \<rightarrow> \<sigma> : L) = ((pi\<bullet>\<tau>) \<rightarrow> (pi\<bullet>\<sigma>) : (pi\<bullet>L))"
 "pi\<bullet>(Union l) = Union (pi\<bullet>l)" 
 "pi\<bullet>latent_eff.NE = latent_eff.NE"
 "pi\<bullet>(Latent S) = Latent (pi\<bullet>S)"

declare perm_ty.simps[eqvt]

lemma perm_ty_latent_eff_ty_list[simp]:
  fixes pi ::"name prm"
  and   \<tau>  ::"ty"
  and   Ts ::"ty list"
  and   l  ::"latent_eff"
  shows "pi\<bullet>\<tau> = \<tau>" and "pi\<bullet>l = l" and "pi\<bullet>Ts = Ts"
  by (induct \<tau> and l rule: ty_latent_eff.inducts) auto

instance ty :: pt_name
by intro_classes auto

instance ty :: fs_name
by intro_classes (simp add: supp_def)

instance latent_eff :: pt_name
by intro_classes auto

instance latent_eff :: fs_name
by intro_classes (simp add: supp_def)

fun
  size_ty :: "ty \<Rightarrow> nat" and
  size_le :: "latent_eff \<Rightarrow> nat" 
where 
  "size_ty (ty.Int) = 1"
| "size_ty (TT) = 1"
| "size_ty (FF) = 1"
| "size_ty (Top) = 1"
| "size_ty (Union []) = 1"
| "size_ty (Union (t#ts)) = size_ty t + size_ty (Union ts)"
| "size_ty (T1 \<rightarrow> T2 : L) = (size_ty T1) + (size_ty T2) + (size_le L)"
| "size_le (Latent L) = size_ty L"
| "size_le (latent_eff.NE) = 1"

lemma size_ty_pos:
  "size_ty T > 0"
proof (induct T )
  fix l
  show "0 < size_ty (Union l)" by (induct l) auto
qed (auto)

nominal_datatype eff = NE | TE "ty" "name" | VE "name" | TT | FF

nominal_datatype builtin = Add1 | NumberP | BooleanP | Nott | ProcP

nominal_datatype trm = 
    Var "name"
  | App "trm" "trm"
  | Abs "\<guillemotleft>name\<guillemotright>trm" "ty"
  | Iff "trm" "trm" "trm"
  | Num "nat"
  | Bool "bool"
  | BI "builtin"

abbreviation
  "lam" :: "name \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" ("Lam [_:_]._" [100,100,100] 100) where
  "Lam[x:T].b \<equiv> trm.Abs x b T"

(* lemmas about names, types, effects *)

lemma trm_finite_supp:
  fixes x::"trm"
  shows "finite ((supp x)::name set)"
  using fs_name_class.axioms[of x] by simp

lemma pt_trm_inst: "pt TYPE(trm) TYPE(name)" using pt_name_inst by auto

lemma fs_trm_inst: "fs TYPE(trm) TYPE(name)" using fs_name_inst by auto

lemma perm_ty_latent[simp]: 
  fixes T::"ty"
  and   le::"latent_eff"
  and   pi::"name prm"
  shows "pi\<bullet>le = le \<and> pi\<bullet>T = T"
  by simp

lemma perm_ty: 
  fixes T::"ty"
  and   le::"latent_eff"
  and   pi::"name prm"
  shows "pi\<bullet>T = T"
  by simp

lemma perm_builtin[simp]: 
  fixes e::"builtin"
  and   pi::"name prm"
  shows "pi\<bullet>e = e"
  by (induct rule: builtin.weak_induct) (simp_all)

lemma fresh_ty[simp]:
  fixes x::"name" 
  and   T::"ty"
  shows "x\<sharp>T"
  by (simp add: fresh_def supp_def)

lemma fresh_latent_eff[simp]:
  fixes x::"name" 
  and   T::"latent_eff"
  shows "x\<sharp>T"
  by (simp add: fresh_def supp_def)

lemma fresh_builtin[simp]:
  fixes x::"name" 
  and   b::"builtin"
  shows "x\<sharp>b"
  by (simp add: fresh_def supp_def)

lemma supp_latent_eff_ty:
  fixes T::ty and le::latent_eff
  shows " supp le = ({}::name set)  \<and> supp T = ({}::name set)"
  by (simp add: supp_def)

text {* size of a term *}

instance trm :: size ..

nominal_primrec
  "size (Var x) = 1"
  "size (BI b) = 1"
  "size (Bool b) = 1"
  "size (Num b) = 1"
  "size (App t1 t2) = (max (size t1) (size t2)) + 1"
  "size (Iff t1 t2 t3) = (max (size t1) (max (size t2) (size t3))) + 1"
  "size (Lam [a:T].t) = (size t) + 1"
  by (auto simp add: fresh_nat, finite_guess+, fresh_guess+)

abbreviation
  "smaller_than_abb" :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<guillemotleft> _" [80,80] 80)
where 
  "a \<guillemotleft> b == size a < size b"

text {* complete induction on terms *}

lemma trm_comp_induct[consumes 0, case_names Var App Lam BI Num Bool Iff]:
  fixes P::"'a::fs_name \<Rightarrow> trm \<Rightarrow> bool"
  and t::"trm"
  and x::"'a::fs_name"
  assumes a1:"!! n z. (!! x t. (t \<guillemotleft> Var n) \<Longrightarrow> P x t) \<Longrightarrow> P z (Var n)"
  and a2:"!! t1 t2 z. (!! x t. (t \<guillemotleft> App t1 t2) \<Longrightarrow> P x t) \<Longrightarrow> (!! x. P x t1) \<Longrightarrow> (!! x . P x t2)
  \<Longrightarrow> P z (App t1 t2)"
  and a3:"!! a b z T. \<lbrakk>a \<sharp> z ; (!! x t. (t \<guillemotleft> Lam[a:T].b)  \<Longrightarrow> P x t)\<rbrakk> \<Longrightarrow> (!! x . P x b) \<Longrightarrow> P z (Lam[a:T].b)"
  and a4:"!! b z. (!! x t. (t \<guillemotleft> BI b) \<Longrightarrow> P x t) \<Longrightarrow> P z (BI b)"
  and a5:"!! n z. (!! x t. (t \<guillemotleft> Num n)  \<Longrightarrow> P x t) \<Longrightarrow> P z (Num n)"
  and a6:"!! b z. (!! x t. (t \<guillemotleft> Bool b) \<Longrightarrow> P x t) \<Longrightarrow> P z (Bool b)"
  and a7:"!! t1 t2 t3 z. (!! x t. t \<guillemotleft> (Iff t1 t2 t3) \<Longrightarrow> P x t) 
  \<Longrightarrow> (!! x. P x t1) \<Longrightarrow> (!! x . P x t2) \<Longrightarrow> (!! x. P x t3) \<Longrightarrow> P z (Iff t1 t2 t3)"
  shows "P x t"
proof (induct t arbitrary: x taking:"(% t :: trm. size t)" rule: measure_induct_rule)
  case (less s x) thus ?case
    -- "This would go through automatically, but I'm skeptical of that sort of thing"
  proof (nominal_induct s avoiding: x rule: trm.induct)
    case (Var v) thus ?case using a1 by auto
  next
    case (App t1 t2) thus ?case using a2 by auto
  next
    case (Abs a b T) thus ?case using a3 by auto
  next
    case (Iff t1 t2 t3) thus ?case using a7 by auto
  next
    case (BI b) thus ?case using a4 by auto
  next
    case (Num n) thus ?case using a5 by auto
  next
    case (Bool b) thus ?case using a6 by auto    
  qed
qed  


text {* closed terms *}

constdefs
fv :: "trm \<Rightarrow> name set"
fv_def[simp]:"fv e == ((supp e):: name set)"

constdefs
  closed :: "trm \<Rightarrow> bool"
  closed_def: "closed e == (fv e = {})"


lemma closed_lam: --"A statement about the free variables of lam bodies"
  assumes "closed (Lam[x:T].b)" (is "closed ?e")
  shows "fv b <= {x}"
  proof -
    have "(supp ([x].b)::name set) = supp b - {x}" 
      using fs_name_class.axioms abs_fun_supp[of b x] pt_trm_inst at_name_inst by auto
    hence "supp ?e = ((((supp b):: name set) - {x}) :: name set)" using supp_latent_eff_ty trm.supp by simp
    thus ?thesis using prems closed_def by auto 
  qed

lemma closed_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "closed e \<Longrightarrow> closed (pi\<bullet>e)"
proof -
  have A:"(pi\<bullet>fv e) = fv (pi\<bullet>e)" using pt_perm_supp[of pi e] at_name_inst pt_trm_inst by auto
  assume "closed e"
  hence "fv e = {}" using closed_def by simp
  hence "(pi\<bullet>fv e) = {}" using empty_eqvt[of pi] by auto
  hence "closed (pi\<bullet>e)" using A closed_def by auto
  thus ?thesis .
qed    


text {* capture-avoiding substitution *}

consts subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100)

nominal_primrec
 "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
 "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
 "x\<sharp>(y,t',T) \<Longrightarrow> (Lam[x:T].t)[y::=t'] = Lam[x:T].(t[y::=t'])"
 "(Iff tst thn els)[y::=t'] = (Iff (tst[y::=t']) (thn[y::=t']) (els[y::=t']))"
 "(BI c)[y::=t'] = (BI c)"
 "(Num c)[y::=t'] = (Num c)"
 "(Bool c)[y::=t'] = (Bool c)"
  by (finite_guess+, auto simp add: abs_fresh, fresh_guess+)

lemma subst_eqvt[simp, eqvt]:
  fixes pi:: "name prm"
  and   t1:: "trm"
  and   t2:: "trm"
  and   a :: "name"
  shows "pi\<bullet>(t1[b::=t2]) = (pi\<bullet>t1)[(pi\<bullet>b)::=(pi\<bullet>t2)]"
by (nominal_induct t1 avoiding: b t2 rule: trm.induct)
   (auto simp add: perm_bij fresh_prod fresh_atm fresh_bij)

lemma subst_rename[rule_format]: 
  shows "c\<sharp>t1 \<longrightarrow> (t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2])"
by (nominal_induct t1 avoiding: a c t2 rule: trm.induct)
   (auto simp add: calc_atm fresh_atm abs_fresh fresh_nat trm.inject perm_nat_def perm_bool)


lemma forget: 
  assumes a: "a\<sharp>t1"
  shows "t1[a::=t2] = t1"
  using a
by (nominal_induct t1 avoiding: a t2 rule: trm.induct)
   (auto simp add: abs_fresh fresh_atm)


lemma subst_removes_var:
  assumes "e1[x::=e0] = e2" and "x \<sharp> e0"
  shows "x \<sharp> e2"
  using prems
proof (nominal_induct e1 avoiding: e0 x e2 rule: trm.induct)
  case (Var v e0' x' e2')
  thus ?case using at_fresh[of x' v] at_name_inst
    by (cases "x' = v") auto
next
  case App thus ?case by auto
next
  case Iff thus ?case by auto
next
  case BI thus ?case by auto
next
  case Num thus ?case by (auto simp add: fresh_nat)
next
  case (Bool b) thus ?case 
    by (auto simp add: fresh_def supp_bool trm.supp)
next
  case (Abs v e1' T e0' x' e2')
  let ?body = "(e1'[x'::=e0'])"
  have a:"finite ((supp ?body) :: name set)" using fs_name1 by auto
  have f:"x' \<sharp> (e1'[x'::=e0'])" using Abs by auto
  hence "v \<sharp> (x',e0',T)" using Abs by auto
  hence "(Abs v e1' T)[x'::=e0'] = Abs v (e1'[x'::=e0']) T" by auto
  hence "\<dots> = e2'" using Abs by auto
  have "v \<noteq> x'" using `v \<sharp> x'` at_fresh[of v x'] at_name_inst by auto
  hence "x' \<sharp> v" using  at_fresh[of x' v] at_name_inst by auto
  have "x' \<sharp> T" using fresh_def supp_latent_eff_ty by auto
  have "x' \<sharp> [v].(e1'[x'::=e0'])" using `v ~= x'` fresh_abs_funI1[of ?body x' v ] pt_trm_inst at_name_inst a f by auto
  hence "x' \<sharp>  Abs v (e1'[x'::=e0']) T" using f trm.fresh Abs by auto
  thus ?case using Abs  by auto
qed
 

lemma fv_lam:
  fixes name
  shows "fv (Lam[name:T].body) =  fv body - {name}"
proof -
  have sT:"supp T = ({} :: name set)" using supp_latent_eff_ty by auto
  have "fv (Lam[name:T].body) = (supp ([name].body):: name set) \<union> supp T" using trm.supp by auto
  also have "\<dots> = (supp ([name].body):: name set)" using sT by auto
  also have "\<dots> = supp body - ({name} :: name set)" 
    using  abs_fun_supp[of body name] at_name_inst pt_trm_inst fs_name1[of body] by simp
  also have "\<dots> = fv body - {name}" by simp
  finally show "fv (Lam[name:T].body) = fv body - {name}" by simp
qed

lemma subst_closed:
  assumes "e1[x::=e0] = e2" and "closed e0"
  shows "fv e2 <= fv e1"
  using prems
proof (nominal_induct e1 avoiding: e0 x e2 rule: trm.induct)
  case (Var v e0' x' e2')
  thus ?case using at_fresh[of x' v] at_name_inst closed_def
    by (cases "x' = v") auto
next
  case (App rator rand e0' x' e2')
  let ?subrator = "rator[x'::=e0']"
  let ?subrand = "rand[x'::=e0']"
  have a:"e2' = App ?subrator ?subrand" using App by simp
  have s1:"fv ?subrator <= fv rator" using App by simp
  have s2:"fv ?subrand <= fv rand" using App by simp
  have b:"fv e2' = fv ?subrator \<union> fv ?subrand" using trm.supp App a by simp
  have d:"fv (App rator rand) = fv rator  \<union> fv rand" using trm.supp by simp
  show ?case using d s1 s2 b by auto
next
  case BI thus ?case by auto
next
  case Num thus ?case by (auto simp add: fresh_nat)
next
  case (Bool b) thus ?case 
    by (auto simp add: fresh_def supp_bool trm.supp)
next
  case (Iff tst thn els e0' x' e2')
  let ?subtst = "tst[x'::=e0']"
  let ?subthn = "thn[x'::=e0']"
  let ?subels = "els[x'::=e0']"
  have a:"e2' = Iff ?subtst ?subthn ?subels" using Iff by simp
  have s1:"fv ?subtst <= fv tst" using Iff by simp
  have s2:"fv ?subthn <= fv thn" using Iff by simp
  have s3:"fv ?subels <= fv els" using Iff by simp
  have b:"fv e2' = fv ?subtst \<union> fv ?subthn \<union> fv ?subels" using trm.supp Iff a by auto
  have d:"fv (Iff tst thn els) = fv tst  \<union> fv thn  \<union> fv els" using trm.supp by auto
  show ?case using d s1 s2 s3 b by auto
next
  case (Abs name body T e0' x' e2')
  have aa:"fv (body[x'::=e0']) \<subseteq> fv body" using Abs by auto
  have a:"fv (Lam[name:T].body) = fv body - {name}" using fv_lam by simp
  have b:"fv (Lam[name:T].(body[x'::=e0'])) = fv (body[x'::=e0']) - {name}" using fv_lam by simp
  have "name \<sharp> (e0',T,x')" using Abs by auto
  hence c:"(Lam[name:T].(body[x'::=e0'])) = (Lam[name:T].(body))[x'::=e0']" by simp
  hence d:"fv e2' = fv (body[x'::=e0']) - {name}" using b Abs by auto
  thus ?case using a aa  by auto
qed


lemma subst_only_var_closed:
  assumes "closed e0" and "fv e1 <= {x}"
  shows "closed (e1[x::=e0])"
proof -
  let ?e2 = "(e1[x::=e0])"
  have a:"fv ?e2 <= {x}" using prems subst_closed[of e1 x e0 ?e2] by auto
  have "x \<sharp> e0" using prems fresh_def[of x e0] closed_def[of e0] by auto
  hence "x \<sharp> ?e2" using subst_removes_var[of e1 x e0 ?e2] by auto
  hence b:"x \<notin> fv ?e2" using fresh_def[of x ?e2] closed_def[of ?e2] by auto
  from a b have "fv ?e2 = {}" by auto
  thus ?thesis using closed_def by simp
qed

lemma beta_closed_closed:
  assumes "closed (Lam[x:T].b)" and "closed v"
  shows "closed (b[x::=v])"
  using prems closed_lam subst_only_var_closed
  by auto


text {* values *}


inductive values :: "trm \<Rightarrow> bool" ("_ : values" [80])
where
  abs_value[simp]: "Lam[x:t].b : values"
|  bi_value[simp]: "BI c : values"
|  num_value[simp]: "Num n : values"
|  bool_value[simp]: "Bool b : values"

equivariance values

abbreviation
  "in_values" :: "trm \<Rightarrow> bool" ("_ \<in> values" [100] 100) where
  "e \<in> values \<equiv> (e : values)"

abbreviation
  "not_in_values" :: "trm \<Rightarrow> bool" ("_ \<notin>  values" [100] 100) where
  "e \<notin> values \<equiv> (~ e : values)"

lemma not_false_eqvt:
  fixes pi :: "name prm"
  and   t  :: "trm"
  assumes a:"t ~= trm.Bool False" and b:"t : values"
  shows "(pi\<bullet>t) ~= trm.Bool False"
  using b a
  by induct (auto simp add: perm_bool)

inductive_cases iff_value:"Iff a b c : values"
inductive_cases app_value:"App a b : values"
inductive_cases var_value:"Var a : values"

nominal_inductive values by (simp add: abs_fresh)

text {* Typing Constants *}

consts
  \<Delta>\<^isub>\<tau> :: "builtin \<Rightarrow> ty"

nominal_primrec
  "\<Delta>\<^isub>\<tau> NumberP = (Top \<rightarrow> BoolTy : Latent ty.Int)"
  "\<Delta>\<^isub>\<tau> BooleanP = (Top \<rightarrow> BoolTy : Latent BoolTy)"
  "\<Delta>\<^isub>\<tau> ProcP = (Top \<rightarrow> BoolTy : Latent (Union [] \<rightarrow> Top : latent_eff.NE))"
  "\<Delta>\<^isub>\<tau> Add1 = (ty.Int \<rightarrow> ty.Int : latent_eff.NE)"
  "\<Delta>\<^isub>\<tau> Nott = (Top \<rightarrow> BoolTy : latent_eff.NE)"
  by simp_all

lemma delta_t_eqvt[eqvt]:
  fixes pi :: "name prm"
  shows "pi \<bullet> \<Delta>\<^isub>\<tau> b = \<Delta>\<^isub>\<tau> (pi \<bullet> b)"
  by (nominal_induct b rule: builtin.induct) auto


(* Delta Function *)

consts
  \<Delta>  :: "builtin \<Rightarrow> trm \<Rightarrow> trm option"
  add1_fun :: "trm \<Rightarrow> trm option"
  nott_fun :: "trm \<Rightarrow> trm option"
  numberp_fun :: "trm \<Rightarrow> bool"
  booleanp_fun :: "trm \<Rightarrow> bool"
  procp_fun :: "trm \<Rightarrow> bool"
  procp_bi_fun :: "builtin \<Rightarrow> bool"

nominal_primrec
  "add1_fun (Num n) = Some (Num (n+1))"
  "add1_fun (Lam[x:ty].b) = None"
  "add1_fun (Iff a b c) = None"
  "add1_fun (App a b) = None"
  "add1_fun (Bool a) = None"
  "add1_fun (BI a) = None"
  "add1_fun (Var a) = None"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  "nott_fun (Num n) = (Some (Bool False))"
  "nott_fun (Lam[x:ty].b) = (Some (Bool False))"
  "nott_fun (Iff a b c) = (Some (Bool False))"
  "nott_fun (App a b) = (Some (Bool False))"
  "nott_fun (Bool b) = Some (Bool (~b))"
  "nott_fun (BI a) = (Some (Bool False))"
  "nott_fun (Var a) = (Some (Bool False))"
  by (auto, finite_guess+, fresh_guess+)
  

nominal_primrec
  "booleanp_fun (Bool b) = True"
  "booleanp_fun (Num n) = False"
  "booleanp_fun (Abs a b c) = False"
  "booleanp_fun (App a b) = False"
  "booleanp_fun (BI c) = False"
  "booleanp_fun (Var v) = False"
  "booleanp_fun (Iff a b c) = False"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  "procp_fun (Bool b) = False"
  "procp_fun (Num n) = False"
  "procp_fun (Abs a b c) = True"
  "procp_fun (App a b) = False"
  "procp_fun (BI c) = True"
  "procp_fun (Var v) = False"
  "procp_fun (Iff a b c) = False"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  "numberp_fun (Bool b) = False"
  "numberp_fun (Num n) = True"
  "numberp_fun (Abs a b c) = False"
  "numberp_fun (App a b) = False"
  "numberp_fun (BI c) = False"
  "numberp_fun (Var v) = False"
  "numberp_fun (Iff a b c) = False"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  "\<Delta> Add1 t = add1_fun t"
  "\<Delta> Nott t = nott_fun t"
  "\<Delta> BooleanP t = Some (Bool (booleanp_fun t))"
  "\<Delta> NumberP t = Some (Bool (numberp_fun t))"
  "\<Delta> ProcP t = Some (Bool (procp_fun t))"
by simp_all


lemma delta_eqvt:
  fixes pi :: "name prm"
  and   b :: builtin
  and   t  :: "trm"
  shows "\<Delta> (pi\<bullet>b) (pi\<bullet>t) = \<Delta> b t"
proof -
  have A:"(pi\<bullet>b) = b" by (nominal_induct b rule: builtin.induct) auto
  have B:"\<Delta> b (pi\<bullet>t) = \<Delta> b t"
  proof (nominal_induct rule: builtin.induct)
    case Add1
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_nat_def)       
  next
    case Nott
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
  next
    case BooleanP
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
  next
    case NumberP
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
  next
    case ProcP
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
  qed
  from A B show ?thesis by auto
qed

lemma delta_eqvt2[eqvt]:
  fixes pi :: "name prm"
  and   b :: builtin
  and   t  :: "trm"
  shows "(pi\<bullet>(\<Delta> b t)) = \<Delta> (pi\<bullet>b) (pi\<bullet>t)"
proof -
  have A:"(pi\<bullet>b) = b" by (nominal_induct b rule: builtin.induct) auto
  have B:"\<Delta> b (pi\<bullet>t) = (pi\<bullet>(\<Delta> b t))"
  proof (nominal_induct rule: builtin.induct)
    case Add1
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_nat_def)       
  next
    case Nott
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
  next
    case BooleanP
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
  next
    case NumberP
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
  next
    case ProcP
    thus ?case 
      by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
  qed
  from A B show ?thesis by auto
qed


lemma delta_closed:
  fixes b :: builtin and t::trm
  assumes "\<Delta> b t = Some v"
  shows "closed v"
  using prems
  proof (nominal_induct b rule: builtin.induct)
    case Add1
    thus ?case 
      by (nominal_induct t rule: trm.induct)
         (auto simp add: supp_nat closed_def trm.supp)
  next
    case Nott
    thus ?case
      by (nominal_induct t rule: trm.induct)
         (auto simp add: supp_def perm_bool closed_def trm.supp)
  next
    case BooleanP
    thus ?case
      by (nominal_induct t rule: trm.induct)
         (auto simp add: supp_def perm_bool closed_def trm.supp)
  next
    case NumberP
    thus ?case
      by (nominal_induct t rule: trm.induct)
         (auto simp add: supp_def perm_bool closed_def trm.supp)
  next
    case ProcP
    thus ?case
      by (nominal_induct t rule: trm.induct)
         (auto simp add: supp_def perm_bool closed_def trm.supp)
       qed

lemma delta_value:
  fixes b :: builtin and t::trm
  assumes "\<Delta> b t = Some v"
  shows "v : values"
  using prems
  proof (nominal_induct b rule: builtin.induct)
    case Add1
    thus ?case by (nominal_induct t rule: trm.induct) auto
  next
    case Nott
    thus ?case
      by (nominal_induct t rule: trm.induct) auto
  next
    case BooleanP
    thus ?case
      by (nominal_induct t rule: trm.induct) auto
  next
    case NumberP
    thus ?case
      by (nominal_induct t rule: trm.induct) auto
  next
    case ProcP
    thus ?case
      by (nominal_induct t rule: trm.induct) auto
  qed

text {* Evaluation contexts *}


inductive_set ctxt :: "(trm \<Rightarrow> trm) set"
where
  C_Hole[simp, intro]: "(%t. t) \<in> ctxt"
|  C_App1[simp, intro]: "E : ctxt \<Longrightarrow> (%t .  (App (E t) u)) : ctxt"
|  C_App2[simp, intro]: "E : ctxt \<Longrightarrow> v : values \<Longrightarrow> (%t . (App v (E t))) : ctxt"
|  C_Iff[simp, intro]: "E : ctxt \<Longrightarrow> (%t . (Iff (E t) thn els)) : ctxt"

lemma ctxt_compose:
  assumes a:"E1 : ctxt" and b:"E2 : ctxt"
  shows "(%t. E1 (E2 t)) : ctxt"
  using a b
  by (induct E1) auto

constdefs
  closed_ctxt :: "(trm \<Rightarrow> trm) \<Rightarrow> bool"
  closed_ctxt_def[simp]:"closed_ctxt C == (C : ctxt \<and> closed (C (Num 3)))" --"3 is a trivially closed term"

lemma ctxt_closed:
  assumes "closed_ctxt C" 
  shows "closed (C e) = closed e"
  using prems
proof -
  have "C : ctxt" using prems by simp
  thus ?thesis using prems
    by (induct) (auto simp add: closed_def trm.supp)
qed  
 
lemma closed_in_ctxt_closed_ctxt:
  assumes "closed e" and a:"C : ctxt" and "e = C L"
  shows "closed L \<and> closed_ctxt C"
  using a prems 
  proof (induct C arbitrary: L e rule: ctxt.induct)
    case C_Hole
    thus ?case by (auto simp add: closed_def trm.supp supp_nat)
  next
    case (C_App1 E arg L' e')
    have IH:"!!e L. \<lbrakk>closed e; E \<in> ctxt; e = E L\<rbrakk> \<Longrightarrow> closed L \<and> closed_ctxt E" using prems by blast
    have cl:"closed (App (E L') arg)" using `e' = (App (E L') arg)` `closed e'` by simp
    from cl have "closed arg"by (auto simp add: closed_def trm.supp)
    from cl have "closed (E L')"  by (auto simp add: closed_def trm.supp)
    thus ?case using IH[of "(E L')" L'] `E : ctxt` `closed arg`
      by (auto simp add: trm.supp closed_def)
  next
    case (C_App2 E rator L' e')
    have IH:"!!e L. \<lbrakk>closed e; E \<in> ctxt; e = E L\<rbrakk> \<Longrightarrow> closed L \<and> closed_ctxt E" using prems by blast
    have cl:"closed (App rator (E L'))" using prems by blast
    from cl have "closed rator" by (auto simp add: closed_def trm.supp)
    from cl have "closed (E L')"  by (auto simp add: closed_def trm.supp)
    thus ?case using IH[of "(E L')" L'] `E : ctxt` `closed rator`
      by (auto simp add: trm.supp closed_def)
  next
    case (C_Iff E thn els L' e')
    let ?trm = "Iff (E L') thn els"
    have IH:"!!e L. \<lbrakk>closed e; E \<in> ctxt; e = E L\<rbrakk> \<Longrightarrow> closed L \<and> closed_ctxt E" using prems by blast
    have cl:"closed ?trm" using prems by blast
    from cl have "closed thn" and "closed els" by (auto simp add: closed_def trm.supp)
    from cl have "closed (E L')"  by (auto simp add: closed_def trm.supp)
    thus ?case using IH[of "(E L')" L'] `E : ctxt` `closed thn` `closed els`
      by (auto simp add: trm.supp closed_def)
  qed

lemma closed_in_ctxt:
  assumes "closed (C L)"
  and "C : ctxt"
  shows "closed L"
  using `C : ctxt` `closed (C L)`
  by (induct C) (auto simp add: closed_def trm.supp)


text{* Reduction *}

inductive reduce :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<hookrightarrow> _" [200,200] 200)
  where
  e_beta[simp]: "v : values \<Longrightarrow> x \<sharp> v \<Longrightarrow> (App (Lam[x:t].b) v) \<hookrightarrow> (b[x::=v])"
  | e_if_false[simp]: "Iff (Bool False) e1 e2 \<hookrightarrow> e2"
  | e_if_true[simp]: "v ~= Bool False \<Longrightarrow> v : values \<Longrightarrow> Iff v e1 e2 \<hookrightarrow> e1"
  | e_delta[simp]: "\<lbrakk>v : values; \<Delta> p v = Some e\<rbrakk> \<Longrightarrow> App (BI p) v \<hookrightarrow> e"

equivariance reduce

nominal_inductive reduce
  by (simp_all add: abs_fresh subst_removes_var)

inductive
  "step" :: "trm\<Rightarrow>trm\<Rightarrow>bool" (" _ \<longrightarrow> _" [80,80]80)
where
  step_one[intro]:"\<lbrakk>E : ctxt; L \<hookrightarrow> R\<rbrakk> \<Longrightarrow> E L \<longrightarrow> E R"

inductive
step_multi :: "trm \<Rightarrow> trm \<Rightarrow> bool" (" _ \<longrightarrow>\<^sup>* _" [80,80] 80)
where 
  sm_refl:"a \<longrightarrow>\<^sup>* a"
| sm_trans:"a \<longrightarrow> b \<Longrightarrow> b \<longrightarrow>\<^sup>* c \<Longrightarrow> a \<longrightarrow>\<^sup>* c"

(* doesn't work *)
(* equivariance step *)


constdefs
reduce_forever :: "trm \<Rightarrow> bool"
"reduce_forever e == \<forall>e' . (e \<longrightarrow>\<^sup>* e') \<longrightarrow> (EX e''. e' \<longrightarrow> e'')"


(* reduction examples *)


lemma "(App (Lam [x:t].(Var x)) (Num 4)) \<hookrightarrow> Num 4"
  proof -
    have "Num 4 : values" "x \<sharp> Num 4" by (auto simp add: fresh_nat)
    hence h:"(App (Lam [x:t].(Var x)) (Num 4)) \<hookrightarrow> ((Var x)[x::=(Num 4)])" by (rule e_beta)
    have "((Var x)[x::=(Num 4)]) = Num 4" by auto
    thus ?thesis using h  by auto
  qed

(* some lemmas about reduction *)


lemma if_val_reduces: 
  assumes a:"tst : values"
  shows "Iff tst thn els \<hookrightarrow> thn \<or> Iff tst thn els \<hookrightarrow> els"
  using a
proof (nominal_induct tst rule: trm.induct)
  case (Bool b) 
  thus ?case using e_if_true e_if_false
    by (cases b) (auto simp add: trm.inject)
qed (auto)

(* a helper lemma - whee abstraction *)
lemma ex_help: 
  assumes a:"e = E t \<and> E : ctxt \<and>  t \<hookrightarrow> t'"
  shows "\<exists>E t t' . e = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
  using a by blast

lemma reduce_in_ctxt:
  fixes e :: trm
  assumes ct:"C : ctxt"
  and ih:"(EX E L R. e = E L \<and> E : ctxt \<and> L \<hookrightarrow> R)"
  shows "(EX E L R. C e = E L \<and> E : ctxt \<and> L \<hookrightarrow> R)"
proof -
  from ih ct obtain Enew tnew t'new where "e = Enew tnew" and  1:"Enew \<in> ctxt" and g1:"tnew \<hookrightarrow> t'new" by auto
  let ?E="(%t . C (Enew t))"
  have g3:"?E tnew = C e" using `e = Enew tnew` by auto
  thus "\<exists>E t t' . C e = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
    using ctxt_compose[OF ct 1] g1 g3 ex_help[of "C e" ?E tnew] by auto
qed

inductive_cases iff_bi_red : "(Iff (Const (BI bi)) thn els) \<hookrightarrow> e"
inductive_cases iff_red : "(Iff tst thn els) \<hookrightarrow> e"

lemma reduce_closed:
  assumes "closed L" and "L \<hookrightarrow> R"
  shows "closed R"
  using `L \<hookrightarrow> R` `closed L`
  proof (induct)
    case (e_beta v x t b) 
    have a:"closed (Abs x b t)" using e_beta closed_def trm.supp by simp
    have b:"closed v" using e_beta closed_def trm.supp by simp
    from a b show ?case using e_beta beta_closed_closed by simp
  next
    case e_if_true thus ?case using closed_def trm.supp by auto
  next
    case e_if_false thus ?case using closed_def trm.supp by auto
  next
    case e_delta thus ?case using delta_closed by auto
  qed


lemma step_closed:
  assumes A:"closed e" and B:"(e :: trm) \<longrightarrow> e'"
  shows "closed e'"
proof - 
  from B obtain E L R where C:"E : ctxt"  "e = E L"  "L \<hookrightarrow> R"  "e' = E R" by induct auto
  hence D:"closed L" "closed_ctxt E" using A closed_in_ctxt_closed_ctxt[of e E L] by auto
  hence "closed R" using C reduce_closed[of L R] by auto
  hence "closed e'" using C D ctxt_closed[of E R] by auto
  thus ?thesis .
qed

lemma multi_step_closed:
  assumes A:"closed e" and B:"e \<longrightarrow>\<^sup>* e'"
  shows "closed e'"
  using B A step_closed
  by induct auto
  



text {* "partial order" (not really) between effects *}

inductive
  subeff :: "eff \<Rightarrow> eff \<Rightarrow> bool"("\<turnstile> _ <e: _" [60,60] 60)
where
  SE_Refl[intro]: "\<turnstile> F <e: F"
| SE_FF[intro]: "F \<noteq> TT \<Longrightarrow> \<turnstile> FF <e: F"
| SE_TT[intro]: "F \<noteq> FF \<Longrightarrow> \<turnstile> TT <e: F"
| SE_VE[intro]: "\<turnstile> NE <e: VE x"
| SE_TE[intro]: "\<turnstile> NE <e: TE S x"

equivariance subeff

inductive_cases ne_case:"\<turnstile> F1 <e: eff.NE"
inductive_cases ne_case_rev:"\<turnstile> eff.NE <e: F1"
inductive_cases tt_case:"\<turnstile> F1 <e: eff.TT"
inductive_cases tt_case_rev:"\<turnstile> eff.TT <e: F1"
inductive_cases ff_case:"\<turnstile> F1 <e: eff.FF"
inductive_cases ff_case_rev:"\<turnstile> eff.FF <e: F1"

lemma no_sub_FF: 
   "\<lbrakk>\<turnstile> T <e: T' ; T' = FF \<rbrakk> \<Longrightarrow> T = FF"
  by (induct rule: subeff.induct) auto

lemma no_sub_TT: 
   "\<lbrakk>\<turnstile> T <e: T' ; T' = TT \<rbrakk> \<Longrightarrow> T = TT"
  by (induct rule: subeff.induct) auto

constdefs
  simple_eff :: "eff \<Rightarrow> bool"
  simple_eff_def[simp]:"simple_eff e == e = eff.NE \<or> e = FF \<or> e = TT"

lemma simple_eff_cases[consumes 1, case_names NE FF TT]:
  fixes F::eff
  and P :: "eff \<Rightarrow> bool"
  assumes a:"simple_eff F"
  and a1:"P NE"
  and a2:"P FF"
  and a3:"P TT"
  shows "P F"
  using prems
by (nominal_induct F rule: eff.induct) auto

lemma simple_eff_below_ne:
  assumes "simple_eff F"
  shows "\<turnstile> F <e: NE"
  using prems
by (nominal_induct F rule: eff.induct) auto


lemma SE_Trans[intro]: 
  assumes"\<turnstile> F1 <e: F2 "and "\<turnstile> F2 <e: F3 " and "simple_eff F1" and "simple_eff F2" and "simple_eff F3"
  shows " \<turnstile> F1 <e: F3"
  using `simple_eff F3` prems
  proof (induct F3 rule: simple_eff_cases)
    case NE thus ?case using simple_eff_below_ne by auto
  next
    case FF thus ?case using no_sub_FF by auto
  next
    case TT thus ?case using no_sub_TT by auto
qed

text{* subtyping *}

inductive
  subtype :: "ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> _ <: _" [60,60] 60)
where
  S_Refl[intro]: "\<turnstile> T <: T"
| S_Fun[intro]: "\<lbrakk>\<turnstile> S1 <: T1 ; \<turnstile> T2 <: S2 ; eff = eff' \<or> eff' = latent_eff.NE\<rbrakk> \<Longrightarrow> \<turnstile> (T1 \<rightarrow> T2 : eff) <: (S1 \<rightarrow> S2 : eff')"
| S_Top[intro]: "\<turnstile> T <: Top"
| S_UnionAbove[intro]: "\<lbrakk>T : set Ts ; \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<turnstile> S <: Union Ts"
| S_UnionBelow[intro]: "\<lbrakk>!! T.( T : set Ts \<Longrightarrow> \<turnstile> T <: S)\<rbrakk> \<Longrightarrow> \<turnstile> Union Ts <: S"

equivariance subtype

nominal_inductive subtype done


inductive_cases sub_arr_cases: "\<turnstile> T <: S1 \<rightarrow> S2 : L"

lemma subtype_arr_elim:
  "\<lbrakk>\<turnstile> T <: S ; S = S0 \<rightarrow> S1 : le\<rbrakk> \<Longrightarrow> (EX T0 T1. T = T0 \<rightarrow> T1 : le \<and> \<turnstile> S0 <: T0 \<and> \<turnstile> T1 <: S1) \<or> (EX T0 T1 le'. T = T0 \<rightarrow> T1 : le' \<and> le = latent_eff.NE \<and> \<turnstile> S0 <: T0 \<and> \<turnstile> T1 <: S1) \<or> (EX Ts. T = Union Ts)"
proof (induct arbitrary: S0 S1  rule: subtype.induct)
  qed (auto)

lemma S_TopE:
  assumes a: "\<turnstile> Top <: T"
  shows "T = Top \<or> (EX Ts T'. T = Union Ts \<and> T' : set Ts \<and> \<turnstile> Top <: T')"
using a by (cases, auto) 

lemma S_ArrowE_left:
  assumes a: "\<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 : L <: T" 
  shows "T = Top \<or> (\<exists>T\<^isub>1 T\<^isub>2. T = T\<^isub>1 \<rightarrow> T\<^isub>2  : L \<and> \<turnstile> T\<^isub>1 <: S\<^isub>1 \<and> \<turnstile> S\<^isub>2 <: T\<^isub>2) \<or> 
  (\<exists>T\<^isub>1 T\<^isub>2. T = T\<^isub>1 \<rightarrow> T\<^isub>2  : latent_eff.NE \<and> \<turnstile> T\<^isub>1 <: S\<^isub>1 \<and> \<turnstile> S\<^isub>2 <: T\<^isub>2) \<or>
  (EX Ts T1. T = Union Ts \<and> T1 : set Ts \<and> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 : L <: T1)"
using a by (cases, auto simp add: ty.inject)

lemma union_size_ty:
  assumes "T : set Ts"
  shows "size_ty T < size_ty (Union Ts)"
  using prems size_ty_pos
  by (induct Ts) auto

fun size_ty3 :: "ty*ty*ty \<Rightarrow> nat"
where 
size_ty3_def[simp]:"size_ty3 (a,b,c) = size_ty a + size_ty b + size_ty c"

inductive_cases union_sub_cases[consumes 1, case_names 1 2 3 4]:"\<turnstile> Union Ts <: S"

lemma union_sub_elim: 
  assumes A:"\<turnstile> Union Ts <: T " (is "\<turnstile> ?S <: T") 
  and B:" T1 : set Ts "
  shows "\<turnstile> T1 <: T"
  using prems
proof (induct "X"=="(T1,?S,T)"  arbitrary: T1 Ts T taking: "size_ty3" rule: measure_induct_rule)
  case (less X)
  show " \<turnstile> T1 <: T" using `\<turnstile>  Union Ts <: T` less 
  proof (induct rule: union_sub_cases)
    case 1 thus ?case by auto
  next
    case 2 thus ?case by auto
  next
    case (3 T' Ts')
    have X_inst:"X = (T1, ty.Union Ts, T)" .
    have "size_ty T' < size_ty T" using 3 union_size_ty by auto
    hence "\<turnstile> T1 <: T'" using X_inst 3(4)[OF _ ` \<turnstile> ty.Union Ts <: T'` `T1 : set Ts`] by auto
    thus ?case using 3 by auto
  next
    case 4 thus ?case by auto
  qed
qed


lemma S_Trans[intro]:
  assumes "\<turnstile>S<:Q" and " \<turnstile>Q<:T"
  shows "\<turnstile>S<:T" 
using prems
proof (induct "X"=="(S,Q,T)"  arbitrary: S Q T taking: "size_ty3" rule: measure_induct_rule)
  case (less X S Q T)
  show " \<turnstile> S <: T" using `\<turnstile> S <: Q` less 
  proof (induct  S Q\<equiv>Q rule: subtype.induct) 
    case S_Refl thus ?case by auto
  next
    case (S_Top A)
    have X_inst:"X = (A,Q,T)" .
    show ?case  
    proof -
      {
	assume "EX Ts T'. T = Union Ts \<and> T' : set Ts \<and> \<turnstile> Q <: T'"
	then obtain Ts T' where "T = Union Ts "" T' : set Ts "" \<turnstile> Q <: T'" by auto
	hence "size_ty T' < size_ty T" using union_size_ty by auto
	hence "size_ty3 (A,Q,T') < size_ty3 (A,Q,T)" by auto
	hence "\<turnstile> A <: T'" using `\<turnstile> A <: Q` `\<turnstile> Q <: T'` using less(1)[of "(A,Q,T')" A Q T'] X_inst by auto
	hence ?thesis using S_Top prems by auto
      }
      thus ?thesis using S_TopE S_Top by auto
    qed
  next
    case (S_Fun Q1 S1 S2 Q2 L L') 
    hence rh_drv: " \<turnstile> Q1 \<rightarrow> Q2 : L' <: T" by simp
    have X_inst:"X = (S1 \<rightarrow> S2 : L, Q1 \<rightarrow> Q2 : L', T)" using S_Fun by auto
    note `Q1 \<rightarrow> Q2 : L' = Q`  
    hence Q12_less: "size_ty Q1 < size_ty Q" "size_ty Q2 < size_ty Q" using size_ty_pos by auto
    have lh_drv_prm1: " \<turnstile> Q1 <: S1" by fact
    have lh_drv_prm2: " \<turnstile> S2 <: Q2" by fact      
    have "T=Top \<or> (\<exists>T1 T2 LL. T=T1\<rightarrow>T2 : LL \<and> \<turnstile>T1<:Q1 \<and> \<turnstile>Q2<:T2 \<and> LL = L') \<or> 
      (\<exists>T1 T2. T=T1\<rightarrow>T2 : latent_eff.NE \<and> \<turnstile>T1<:Q1 \<and> \<turnstile>Q2<:T2) \<or>
      (EX Ts T1. T = Union Ts \<and> T1 : set Ts \<and> \<turnstile> Q1 \<rightarrow> Q2 : L' <: T1)" 
      using S_ArrowE_left[OF rh_drv] by auto
    moreover
    { 
      assume "\<exists>T1 T2 LL. T=T1\<rightarrow>T2:LL \<and> \<turnstile>T1<:Q1 \<and> \<turnstile>Q2<:T2 \<and> LL = L'"
      then obtain T1 T2 LL
	where T_inst: "T = T1 \<rightarrow> T2 : L'" 
	and   rh_drv_prm1: " \<turnstile> T1 <: Q1"
	and   rh_drv_prm2: " \<turnstile> Q2 <: T2"
	and   LL': "LL = L'" by auto
      from X_inst T_inst have X_inst':"X = (S1 \<rightarrow> S2 : L, Q1 \<rightarrow> Q2 : L', T1 \<rightarrow> T2 : L')" by simp
      hence "size_ty3 (T1, Q1, S1) < size_ty3 X" using size_ty_pos by auto     
      from X_inst' lh_drv_prm1  rh_drv_prm1 have  " \<turnstile> T1 <: S1" using S_Fun(6)[of _ T1 Q1 S1] size_ty_pos by auto
      moreover
      from X_inst' lh_drv_prm2  rh_drv_prm2 have " \<turnstile> S2 <: T2" using S_Fun(6)[of _ S2 Q2   T2] size_ty_pos by auto
      ultimately have " \<turnstile> S1 \<rightarrow> S2 : L <: T1 \<rightarrow> T2 : LL" using LL' S_Fun by (simp add: subtype.S_Fun)
      hence " \<turnstile> S1 \<rightarrow> S2 : L <: T" using T_inst LL' by simp
    }
    moreover 
    { 
      assume "EX Ts T1. T = Union Ts \<and> T1 : set Ts \<and> \<turnstile> Q1 \<rightarrow> Q2 : L' <: T1"
      then obtain Ts T1
	where T_inst: "T = Union Ts"
	and elem: "T1 : set Ts"
	and sub:"\<turnstile> Q1 \<rightarrow> Q2 : L' <: T1"
	by auto
      have sub':"\<turnstile> S1 \<rightarrow> S2 : L <:  Q1 \<rightarrow> Q2 : L'" using S_Fun by simp
      have sz:"size_ty T1 < size_ty T" using T_inst elem union_size_ty by auto
      from X_inst T_inst have X_inst':"X = (S1 \<rightarrow> S2 : L, Q1 \<rightarrow> Q2 : L', Union Ts)" by simp
      from sub sub' X_inst' 
      have " \<turnstile> S1 \<rightarrow> S2 : L <: T1"  using S_Fun(6)[OF _ sub' sub]  sz T_inst by auto
      hence " \<turnstile> S1 \<rightarrow> S2 : L <: T"  using T_inst elem S_UnionAbove by auto      
    }
    moreover
    {
      assume "\<exists>T1 T2. T=T1\<rightarrow>T2:latent_eff.NE \<and> \<turnstile>T1<:Q1 \<and> \<turnstile>Q2<:T2 "
      then obtain T1 T2 LL
	where T_inst: "T = T1 \<rightarrow> T2 : latent_eff.NE" 
	and   rh_drv_prm1: " \<turnstile> T1 <: Q1"
	and   rh_drv_prm2: " \<turnstile> Q2 <: T2"
	 by auto
      from X_inst T_inst have X_inst':"X = (S1 \<rightarrow> S2 : L, Q1 \<rightarrow> Q2 : L', T1 \<rightarrow> T2 : latent_eff.NE)" by simp
      hence "size_ty3 (T1, Q1, S1) < size_ty3 X" using size_ty_pos by auto     
      from X_inst' lh_drv_prm1  rh_drv_prm1 have  " \<turnstile> T1 <: S1" using S_Fun(6)[of _ T1 Q1 S1] size_ty_pos by auto
      moreover
      from X_inst' lh_drv_prm2  rh_drv_prm2 have " \<turnstile> S2 <: T2" using S_Fun(6)[of _ S2 Q2   T2] size_ty_pos by auto
      ultimately have " \<turnstile> S1 \<rightarrow> S2 : L <: T1 \<rightarrow> T2 : latent_eff.NE" using  S_Fun by (simp add: subtype.S_Fun)
      hence " \<turnstile> S1 \<rightarrow> S2 : L <: T" using T_inst  by simp
    }
    ultimately show " \<turnstile> S1 \<rightarrow> S2 : L <: T" by blast
  next
    case (S_UnionAbove T1 Ts S)
    have sub1:"\<turnstile> S <: T1" .
    hence sub2:"\<turnstile> T1 <: T" using S_UnionAbove union_sub_elim[of Ts T T1] by auto
    have sz:"size_ty T1 < size_ty Q" using S_UnionAbove union_size_ty by auto
    hence "\<turnstile> S <: T" using S_UnionAbove(4)[OF _ sub1 sub2] sz S_UnionAbove(7) by auto
    thus ?case .
  next
    case (S_UnionBelow Ts S)
    have "!! T0. T0 : set Ts \<Longrightarrow> \<turnstile> T0 <: T"
      proof -
	fix T0
	assume "T0 : set Ts"
	hence sz:"size_ty T0 < size_ty (Union Ts)" using union_size_ty by auto
	have s1:"\<turnstile> T0 <: S" using S_UnionBelow `T0 : set Ts` by auto
	have s2:"\<turnstile> S <: T" using S_UnionBelow by auto
	note S_UnionBelow(6)
	thus "\<turnstile> T0 <: T" using S_UnionBelow(3)[OF _ s1 s2] sz `S = Q` by auto
      qed
    thus ?case ..
  qed
qed


text {* type environments *}

types varEnv = "(name*ty) list"

text {* valid contexts *}
inductive
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
    v1[intro]: "valid []"
  | v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

equivariance valid

nominal_inductive valid done

lemma fresh_context[rule_format]: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    a :: "name"
  assumes a: "a\<sharp>\<Gamma>"
  shows "\<not>(\<exists>\<tau>::ty. (a,\<tau>)\<in>set \<Gamma>)"
using a
by (induct \<Gamma>)
   (auto simp add: fresh_prod fresh_list_cons fresh_atm)

lemma valid_elim: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    pi:: "name prm"
  and    a :: "name"
  and    \<tau> :: "ty"
  shows "valid ((a,\<tau>)#\<Gamma>) \<Longrightarrow> valid \<Gamma> \<and> a\<sharp>\<Gamma>"
by (ind_cases "valid ((a,\<tau>)#\<Gamma>)") simp

lemma valid_unicity[rule_format]: 
  assumes a: "valid \<Gamma>"
  and     b: "(c,\<sigma>)\<in>set \<Gamma>"
  and     c: "(c,\<tau>)\<in>set \<Gamma>"
  shows "\<sigma>=\<tau>" 
using a b c
by (induct \<Gamma>) (auto dest!: valid_elim fresh_context)

declare fresh_list_cons[simp]
declare fresh_list_nil[simp]

(* environment operations *)

consts 
  env_plus :: "eff \<Rightarrow> varEnv => varEnv"
  env_minus :: "eff \<Rightarrow> varEnv => varEnv"

(* original type is the SECOND argument *)

constdefs
less_ty :: "((ty * ty) * ty * ty) set"
"less_ty == {((a,b),c,d) . (size_ty b) < (size_ty d)}"

function (sequential)
  restrict :: "ty \<Rightarrow> ty \<Rightarrow> ty"
where
  restrict_union: "restrict r (Union (ls :: ty list)) = 
  (if (\<turnstile> r <: Union ls) then r else (if (\<turnstile> Union ls <: r) then (Union ls) else Union (map (restrict r) ls)))"
| restrict_top:"restrict r Top = r"
| restrict_other:"restrict r T = (if (\<turnstile> r <: T) then r else T)"
  by pat_completeness auto
termination using union_size_ty
  by (relation "measure (% (a,b). size_ty b)") auto

lemma restrict_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(restrict T1 T2) = restrict (pi\<bullet>T1) (pi\<bullet>T2)"
by (induct T2) (auto)

text {* this is the key lemma in the whole soundness proof *}

fun simple_ty :: "ty \<Rightarrow> bool"
where
  "simple_ty ty.Int = True"
|  "simple_ty ty.TT = True"
|  "simple_ty ty.FF = True"
|  "simple_ty (A1 \<rightarrow> A2 : L) = True"
(* |  "simple_ty (Union [ty.TT,ty.FF]) = True" *)
|  "simple_ty T = False"

lemma ty_cases[consumes 0, case_names Top Int TT FF Arr Union]:
  fixes P :: "ty \<Rightarrow> bool"
  and T :: ty
  assumes a1:"P Top"
  and a2:"P ty.Int"
  and a3:"P ty.TT"
  and a3':"P ty.FF"
  and a4:"!! t1 t2 L. P (t1 \<rightarrow> t2 : L)"
  and a5:"!! Ts . P (Union Ts)"
  shows "P T"
  using  ty_latent_eff.induct[of P "(%e . True)" "(%e . True)" T] prems
  by auto

inductive_cases tt_below_union:  "\<turnstile> ty.TT <: ty.Union Ts"
inductive_cases ff_below_union:  "\<turnstile> ty.FF <: ty.Union Ts"

(* I believe this to be true without C, but it's easier to prove this way, and that's all we need *)
lemma restrict_soundness:
  assumes A:"\<turnstile> T0 <: T"
  and B:"\<turnstile> T0 <: S"
  and C:"simple_ty T0"
  shows "\<turnstile> T0 <: restrict S T"
  using prems
proof (induct T arbitrary: S T0 taking:"size_ty" rule: measure_induct_rule)
  case (less T S T0)
  thus ?case
  proof (induct T==T rule: ty_cases)
    case Top thus ?case by auto
  next
    case Int thus ?case by auto
  next
    case TT thus ?case by auto
  next
    case FF thus ?case by auto
  next
    case Arr thus ?case by auto
  next
    case (Union Ts)
    have r:"restrict S T = (if (\<turnstile> S <:T) then S else (if (\<turnstile> T <: S) then T else Union (map (restrict S) Ts)))" 
      using prems restrict_union[of S Ts] by auto
    thus ?case
    proof -
      {
	assume "\<turnstile> S <: T"
	hence "restrict S T = S" using r by simp	
	hence ?thesis using prems by auto
      }
      moreover
      {
	assume "\<turnstile> T <: S" "~ (\<turnstile> S <: T)"
	hence "restrict S T = T" using r by simp	
	hence ?thesis using prems by auto
      }
      moreover
      {
	assume "~ (\<turnstile> T <: S)" "~ (\<turnstile> S <: T)"
	hence req:"restrict S T =  Union (map (restrict S) Ts)" using r by auto
	have T:"\<turnstile> T0 <: Union Ts" using prems by simp
	have "?this \<Longrightarrow> ?thesis"
	proof (ind_cases "\<turnstile> T0 <: Union Ts")
	  assume 0:"Union Ts = T0" thus ?thesis using `simple_ty T0` by (induct T0 rule: simple_ty.induct) auto
	next
	  fix Ts'
	  assume "T0 = ty.Union Ts'" thus ?thesis using `simple_ty T0` by (induct T0 rule: simple_ty.induct) auto
(* 
	  hence 1:"T0 = Union [ty.TT,ty.FF]" using `simple_ty T0` by (induct T0 rule: simple_ty.induct) auto

          have "\<turnstile> ty.TT <: T0" using 1 by auto
          hence "\<turnstile> ty.TT <: Union Ts" "\<turnstile> ty.TT <: T" "\<turnstile> ty.TT <: S" using T `\<turnstile> T0 <: S` `\<turnstile> T0 <: T` by auto
          hence "EX \<sigma> . \<sigma> : set Ts \<and> \<turnstile> ty.TT <: \<sigma>" using tt_below_union by auto
          then guess \<sigma> by auto
          hence "size_ty \<sigma> < size_ty T" using prems union_size_ty by auto
          note prems(4)[OF `size_ty \<sigma> < size_ty T` `\<turnstile> ty.TT <: \<sigma>` `\<turnstile> ty.TT <: S`, simplified]
          hence A_tt:"\<turnstile> ty.TT <: restrict S \<sigma>" .
          have mem:"restrict S \<sigma> : set (map (restrict S) Ts)" using `\<sigma> : set Ts` by auto
          hence "\<turnstile> ty.TT <: Union (map (restrict S) Ts)" using A_tt S_UnionAbove by auto
          hence tt_sub:"\<turnstile> ty.TT <: restrict S T" using req by auto

          have "\<turnstile> ty.FF <: T0" using 1 by auto
          hence "\<turnstile> ty.FF <: Union Ts" "\<turnstile> ty.FF <: T" "\<turnstile> ty.FF <: S" using T `\<turnstile> T0 <: S` `\<turnstile> T0 <: T` by auto
          hence "EX \<sigma> . \<sigma> : set Ts \<and> \<turnstile> ty.FF <: \<sigma>" using ff_below_union by auto
          then guess \<sigma> by auto
          hence "size_ty \<sigma> < size_ty T" using prems union_size_ty by auto
          note prems(4)[OF `size_ty \<sigma> < size_ty T` `\<turnstile> ty.FF <: \<sigma>` `\<turnstile> ty.FF <: S`, simplified]
          hence A_ff:"\<turnstile> ty.FF <: restrict S \<sigma>" .
          have mem:"restrict S \<sigma> : set (map (restrict S) Ts)" using `\<sigma> : set Ts` by auto
          hence "\<turnstile> ty.FF <: Union (map (restrict S) Ts)" using A_ff S_UnionAbove by auto
          hence ff_sub:"\<turnstile> ty.FF <: restrict S T" using req by auto

          from ff_sub tt_sub have "\<turnstile> Union [ty.TT, ty.FF] <: restrict S T" by auto
          thus ?thesis using 1 by auto
*)
        next
	  fix T'
	  assume "T' : set Ts" "\<turnstile> T0 <: T'"
	  have 1:"\<turnstile> T0 <: restrict S T'" using union_size_ty prems by auto
	  have 2:"set (map (restrict S) Ts) =  (restrict S) ` set Ts" by auto
	  have 3:"T' : set Ts" using prems by auto
	  have 4:"restrict S T' : set (map (restrict S) Ts)" using 2 3 by auto
	  hence "\<turnstile> T0 <: Union (map (restrict S) Ts)" using subtype.S_UnionAbove[OF 4 1] by auto
	  thus ?thesis using req by auto
	qed
	hence ?thesis using T by simp
      }
      ultimately show ?thesis by auto
    qed
  qed
qed

function (sequential)
  remove :: "ty \<Rightarrow> ty \<Rightarrow> ty"
where
  remove_union: "remove r (Union (ls :: ty list)) = (if (\<turnstile> Union ls <: r) then (Union []) else Union (map (remove r) ls))"
| remove_other:"remove r T = (if (\<turnstile> T <: r) then (Union []) else T)"
  by pat_completeness auto
termination using union_size_ty
  by (relation "measure (% (a,b). size_ty b)") auto

lemma remove_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(remove T1 T2) = remove (pi\<bullet>T1) (pi\<bullet>T2)"
by (induct T2) (auto)

lemma remove_soundness:
  assumes A:"\<turnstile> T0 <: T" and B:"~ (\<turnstile> T0 <: S)" and C:"simple_ty T0"
  shows "\<turnstile> T0 <: remove S T"
  using prems
proof (induct T arbitrary: S T0 taking:"size_ty" rule: measure_induct_rule)
  case (less T S T0)
  thus ?case
  proof (induct T==T rule: ty_cases)
    case (Union Ts)
    have r:"remove S T = (if (\<turnstile> T <:S) then (Union []) else  Union (map (remove S) Ts))" 
      using prems remove_union[of S Ts] by auto
    thus ?case
    proof -
      {
	assume "\<turnstile> T <: S"
	hence "remove S T = (Union [])" using r by simp	
	hence ?thesis using prems by auto
      }
      moreover
      {
	assume "~ (\<turnstile> T <: S)" 
	hence req:"remove S T =  Union (map (remove S) Ts)" using r by auto
	have T:"\<turnstile> T0 <: Union Ts" using prems by simp
	have "?this \<Longrightarrow> ?thesis"
	proof (ind_cases "\<turnstile> T0 <: Union Ts")
	  assume 0:"Union Ts = T0" thus ?thesis using `simple_ty T0` by auto
	next
	  fix Ts'
	  assume "T0 = ty.Union Ts'"
	  thus ?thesis using `simple_ty T0` by auto
	next
	  fix T'
	  assume "T' : set Ts" "\<turnstile> T0 <: T'"
	  have 1:"\<turnstile> T0 <: remove S T'" using union_size_ty prems by auto
	  have 2:"set (map (remove S) Ts) =  (remove S) ` set Ts" by auto
	  have 3:"T' : set Ts" using prems by auto
	  have 4:"remove S T' : set (map (remove S) Ts)" using 2 3 by auto
	  hence "\<turnstile> T0 <: Union (map (remove S) Ts)" using subtype.S_UnionAbove[OF 4 1] by auto
	  thus ?thesis using req by auto
	qed
	hence ?thesis using T by simp
      }
      ultimately show ?thesis by auto
    qed
  qed (auto)
qed

lemma restrict_remove_soundness:
  assumes A:"\<turnstile> T0 <: T" and B:"simple_ty T0"
  shows
  "(\<turnstile> T0 <: S \<and> \<turnstile> T0 <: restrict S T) \<or> (~ (\<turnstile> T0 <: S) \<and> \<turnstile> T0 <: remove S T)"
using restrict_soundness[OF A _ B] remove_soundness[OF A _ B]
by auto

fun replace :: "ty \<Rightarrow> ty \<Rightarrow> ty"
where
  "replace t u = t"

fun mapfun :: "(ty \<Rightarrow> ty \<Rightarrow> ty) \<Rightarrow> ty \<Rightarrow> name \<Rightarrow> (name*ty) \<Rightarrow> (name * ty)"
where
mapfun_def: "mapfun f T x (v,S) =  (if (x = v) then (v, f T S) else (v,S))" 


constdefs
  envop :: "(ty \<Rightarrow> ty \<Rightarrow> ty) \<Rightarrow> name \<Rightarrow> ty \<Rightarrow> (name*ty) list \<Rightarrow> (name*ty) list"
  envop_def[simp]:"envop f n t G == map (% (v,ty). (if (n = v) then (v,f t ty) else (v,ty))) G"

lemma envop_mapfun:
  shows "map (mapfun f T x) \<Gamma> = envop f x T \<Gamma> " using mapfun_def by auto

lemma envop_fresh:
  fixes v::name
  assumes a:"v \<sharp> \<Gamma>"  and c:"valid \<Gamma>"
  shows "v \<sharp> (envop f n t \<Gamma>)"
  using c a
  by (induct \<Gamma> rule: valid.induct) auto

lemma envop_valid:
  assumes "valid \<Gamma>"
  shows "valid (envop f n t \<Gamma>)"
  using assms envop_fresh
  by induct auto

lemma envop_forget:
  assumes "valid \<Gamma>" and "x \<sharp> \<Gamma>"
  shows "envop f x T \<Gamma> = \<Gamma>"
  using prems
  proof (induct rule: valid.induct)
    case v1 thus ?case by auto
  next
    case (v2 \<Gamma>' a S)
    have "x ~= a" and "x \<sharp> \<Gamma>'" using v2 fresh_list_cons fresh_atm[of x a] by auto
    hence A:"envop f x T ((a,S)#\<Gamma>') = (a,S)# (envop f x T \<Gamma>')" by auto
    thus ?case using v2 `x \<sharp> \<Gamma>'` by auto
  qed
    

nominal_primrec 
  "env_plus (NE) G = G"
  "env_plus (TE T x) G = envop restrict x T G"
  "env_plus (VE x) G = envop remove x (ty.FF) G"
  "env_plus (TT) G = G"
  "env_plus (FF) G = G"
  by auto

lemma map_eqvt[eqvt]:
  fixes pi::"name prm"
  and   l::"('a::pt_name) list"
  shows "pi\<bullet>(map f l) = map (pi\<bullet>f) (pi\<bullet>l)"
  by (induct l) perm_simp+

lemma env_plus_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(env_plus X G ) = env_plus (pi\<bullet>X) (pi\<bullet>G)"
proof (nominal_induct X rule: eff.induct)
  case (TE T x) thus ?case by (perm_simp add: eqvts split_def) auto
next
  case (VE x) thus ?case by (perm_simp add: eqvts split_def) auto
qed(auto)

nominal_primrec
  "env_minus (NE) G = G"
  "env_minus (TE T x) G = envop remove x T G"
  "env_minus (VE x) G = envop replace x ty.FF G"
  "env_minus (TT) G = G"
  "env_minus (FF) G = G"
  by auto

lemma env_minus_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(env_minus X G) = env_minus (pi\<bullet>X) (pi\<bullet>G)"
proof (nominal_induct X rule: eff.induct)
  case (TE T x) thus ?case
    by (perm_simp add: eqvts perm_fun_def split_def) auto
  case (VE x) thus ?case
    by (perm_simp add: eqvts perm_fun_def split_def) 
qed(auto)

abbreviation   env_plus_syn :: "varEnv \<Rightarrow> eff \<Rightarrow> varEnv" ("_ |+ _"  [70,70] 70)
where
  "(G |+ eff) == env_plus eff G"

abbreviation env_minus_syn :: "varEnv \<Rightarrow> eff \<Rightarrow> varEnv" ("_ |- _"  [70,70] 70)
where
  "(G |- eff) == env_minus eff G"

--"Induction principle for type envs"
lemma env_induct[case_names Nil Cons]:
  fixes \<Gamma> :: varEnv
  assumes a1:"P []"
  and     a2:"!!G v T. P G \<Longrightarrow> P ((v,T)#G)"
  shows "P \<Gamma>"
  using a1 a2
  by (induct \<Gamma>) auto

lemma envop_eqvt:
  fixes pi::"name prm"
  shows  "envop f (pi\<bullet>n) T (pi\<bullet>\<Gamma>) = (pi\<bullet> (envop f n T \<Gamma>))"
  proof (induct \<Gamma> rule: env_induct)
    case Nil thus ?case by auto
  next
    case (Cons  G v T0) thus ?case using pt_bij4[of pi n v] pt_name_inst at_name_inst by auto
  qed
 
lemma env_plus_eqvt:
  fixes pi::"name prm"
  shows "(pi\<bullet>\<Gamma>) |+ pi\<bullet>eff = pi\<bullet>(\<Gamma> |+ eff)"
  by (nominal_induct eff avoiding: \<Gamma> rule: eff.induct)
   (auto simp add: eff.eqvts envop_eqvt simp del: envop_def)

lemma env_minus_eqvt:
  fixes pi::"name prm"
  shows "(pi\<bullet>\<Gamma>) |- pi\<bullet>eff = pi\<bullet>(\<Gamma> |- eff)"
  by (nominal_induct eff avoiding: \<Gamma> rule: eff.induct)
     (auto simp add: eff.eqvts envop_eqvt simp del: envop_def)


lemma env_plus_simple_eff:
  assumes "simple_eff eff"
  shows "\<Gamma> |+ eff = \<Gamma>"
  using prems 
  by (induct eff rule: simple_eff_cases) auto
  
lemma env_minus_simple_eff:
  assumes "simple_eff eff"
  shows "\<Gamma> |- eff = \<Gamma>"
  using prems
  by (induct eff rule: simple_eff_cases) auto

fun comb_eff :: "eff \<Rightarrow> eff \<Rightarrow> eff \<Rightarrow> eff"
where
  "comb_eff F1 F2 F3 = eff.NE"

lemma comb_eff_eqvt[eqvt]:
  fixes pi :: "name prm"
  shows "(pi\<bullet> (comb_eff F1 F2 F3)) = comb_eff (pi\<bullet>F1) (pi\<bullet>F2) (pi\<bullet>F3) "
  using comb_eff.simps by auto

text {* type judgments *}
inductive
  typing :: "varEnv \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> eff \<Rightarrow> bool" (" _ \<turnstile> _ : _ ; _ " [60,60,60,60] 60) 
where
  T_Var[intro]:   "\<lbrakk>valid \<Gamma>; (v,T)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var v : T ; VE v" 
| T_Const[intro]: "valid \<Gamma> \<Longrightarrow> \<Delta>\<^isub>\<tau> b = T \<Longrightarrow> \<Gamma> \<turnstile> (BI b) : T ; TT"
| T_Num[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Num n) : ty.Int ; TT"
| T_True[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Bool True) : ty.TT ; TT"
| T_False[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Bool False) : ty.FF ; FF"
| T_Abs[intro]:   "\<lbrakk>x \<sharp> \<Gamma>; ((x,T1)#\<Gamma>) \<turnstile> b : T2; eff\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x:T1].b : (T1\<rightarrow>T2 : latent_eff.NE) ; TT"
| T_App[intro]: "\<lbrakk>(\<Gamma> \<turnstile> e1 : U ; eff1) ; \<turnstile> U <: (T0 \<rightarrow> T1 : le); (\<Gamma> \<turnstile> e2 : T; eff2) ;  \<turnstile> T <: T0\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : T1 ; NE"
| T_AppPred[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : U; eff1; \<turnstile> U <: (T0 \<rightarrow> T1 : Latent S);  \<Gamma> \<turnstile> e2 : T; VE x ;  \<turnstile> T <: T0\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : T1 ; TE S x"
| T_If[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : T1; eff1; (\<Gamma> |+ eff1) \<turnstile> e2 : T2; eff2; (\<Gamma> |- eff1) \<turnstile> e3 : T3; eff3; \<turnstile> T2 <: T; \<turnstile> T3 <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Iff e1 e2 e3) : T ; comb_eff eff1 eff2 eff3"
| T_AppPredTrue[intro]: 
  "\<lbrakk>\<Gamma> \<turnstile> e1 : U; eff1; \<turnstile> U <: (T0 \<rightarrow> T1 : Latent S); \<Gamma> \<turnstile> e2 : T; eff2 ;  \<turnstile> T <: T0; \<turnstile> T <: S\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : T1 ; TT"
| T_AppPredFalse[intro]:
  "\<lbrakk>\<Gamma> \<turnstile> e1 : U; eff1; \<turnstile> U <: (T0 \<rightarrow> T1 : Latent S); \<Gamma> \<turnstile> e2 : T; eff2 ;  \<turnstile> T <: T0; ~(\<turnstile> T <: S) ; e2 : values ; closed e2\<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : T1 ; FF"
| T_IfTrue[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; TT ; \<Gamma> \<turnstile> e2 : T2 ; eff;  \<turnstile> T2 <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Iff e1 e2 e3) : T ; NE" 
| T_IfFalse[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; FF ; \<Gamma> \<turnstile> e3 : T3 ; eff;  \<turnstile> T3 <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Iff e1 e2 e3) : T ; NE"
| T_AbsPred[intro]:   "\<lbrakk>x \<sharp> \<Gamma>; ((x,T1)#\<Gamma>) \<turnstile> b : T2; TE S x\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x:T1].b : (T1\<rightarrow>T2 : Latent S) ; TT"

equivariance typing

nominal_inductive typing 
  by (auto simp add: abs_fresh)

text {* then we begin on preservation *}

abbreviation
  "sub" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" (" _ \<lless> _ " [80,80] 80) where
  "\<Gamma>1 \<lless> \<Gamma>2 \<equiv> \<forall>a \<sigma>. (a,\<sigma>)\<in>set \<Gamma>1 \<longrightarrow>  (a,\<sigma>)\<in>set \<Gamma>2"

lemma envplus_empty:
  shows "env_plus eff [] = []"
  by (nominal_induct rule: eff.induct) auto
lemma envminus_empty:
  shows "env_minus eff [] = []"
  by (nominal_induct rule: eff.induct) auto

lemma w_lem1:
  fixes \<Gamma> \<Gamma>'
  assumes "\<Gamma> \<lless> \<Gamma>'" and a:"valid \<Gamma>'"
  shows "map f \<Gamma> \<lless> map f \<Gamma>'"
proof -
  let ?mapfun = f
  from prems have "set \<Gamma> <= set \<Gamma>'" by auto
  hence "set (map ?mapfun \<Gamma>) <= set (map ?mapfun \<Gamma>')" by auto
  hence "(map ?mapfun \<Gamma>) \<lless> (map ?mapfun \<Gamma>')" by blast
  thus ?thesis .
qed
  
  

lemma weakening_envplus: 
  assumes b:"\<Gamma> \<lless> \<Gamma>'" and a:"valid \<Gamma>'"
  shows "env_plus eff \<Gamma> \<lless> env_plus eff \<Gamma>'"
  using a prems w_lem1[of \<Gamma> \<Gamma>']
  by (nominal_induct eff avoiding: \<Gamma> \<Gamma>' rule: eff.induct) auto

lemma weakening_envminus: 
  assumes "\<Gamma> \<lless> \<Gamma>'" and a:"valid \<Gamma>'" and b:"valid \<Gamma>"
  shows "env_minus eff \<Gamma> \<lless> env_minus eff \<Gamma>'"
  using a prems w_lem1[of \<Gamma> \<Gamma>']
  by (nominal_induct eff avoiding: \<Gamma> \<Gamma>' rule: eff.induct) auto

lemma envplus_valid:
  assumes "valid \<Gamma>"
  shows "valid (\<Gamma> |+ F)"
  using prems
proof (induct rule: valid.induct)
  case v1 thus ?case using envplus_empty by auto
next
  case (v2 \<Gamma>' a T) 

  from v2 show ?case
  proof (nominal_induct rule: eff.induct)
    case (TE S x)
    let ?op = "restrict"
    let ?G = "((a, T) # \<Gamma>')"
    let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op S ty) else (v,ty)))"
    have C:"valid (map ?mapfun \<Gamma>')" using v2 `valid (\<Gamma>' |+ TE S x)` by auto
    hence D:"a \<sharp> (map ?mapfun \<Gamma>')" using v2 envop_fresh `valid (\<Gamma>' |+ TE S x)` by auto
    thus ?case
    proof (cases "a = x")
      case False
      from D have E:"valid ((a,T)# (map ?mapfun \<Gamma>'))" using C by auto
      from False have B:"?G |+ TE S x = ((a,T)# (map ?mapfun \<Gamma>'))" by auto
      thus ?thesis using E by auto
    next
      case True
      hence B:"?G |+ TE S x = ((a,?op S T)# (map ?mapfun \<Gamma>'))" by auto
      from D have E:"valid ((a,?op S T)# (map ?mapfun \<Gamma>'))" using C by auto
      thus ?thesis using B by auto
    qed
  next
    case (VE x) 
    thus ?case 
    proof -
      let ?op = "remove"
      let ?G = "((a, T) # \<Gamma>')"
      let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op ty.FF ty) else (v,ty)))"
      have C:"valid (map ?mapfun \<Gamma>')" using v2 `valid (\<Gamma>' |+ VE x)` by auto
      hence D:"a \<sharp> (map ?mapfun \<Gamma>')" using v2 envop_fresh `valid (\<Gamma>' |+ VE x)` by auto
      thus ?case
      proof (cases "a = x")
	case False
	from D have E:"valid ((a,T)# (map ?mapfun \<Gamma>'))" using C by auto
	from False have B:"?G |+ VE x = ((a,T)# (map ?mapfun \<Gamma>'))" by auto
	thus ?thesis using E by auto
      next
	case True
	hence B:"?G |+ VE x = ((a,?op ty.FF T)# (map ?mapfun \<Gamma>'))" by auto
	from D have E:"valid ((a,?op ty.FF T)# (map ?mapfun \<Gamma>'))" using C by auto
	thus ?thesis using B by auto
      qed
    qed
  qed (auto)
qed

lemma envminus_valid:
  assumes "valid \<Gamma>"
  shows "valid (\<Gamma> |- F)"
  using prems 
proof (induct rule: valid.induct)
  case v1 thus ?case using envminus_empty by auto
next
  case (v2 \<Gamma>' a T) thus ?case
  proof (nominal_induct rule: eff.induct)
    case (TE S x)
    let ?op = "remove"
    let ?G = "((a, T) # \<Gamma>')"
    let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op S ty) else (v,ty)))"
    have C:"valid (map ?mapfun \<Gamma>')" using v2 `valid (\<Gamma>' |- TE S x)` by auto
    hence D:"a \<sharp> (map ?mapfun \<Gamma>')" using v2 envop_fresh `valid (\<Gamma>' |- TE S x)` by auto
    thus ?case
    proof (cases "a = x")
      case False
      from D have E:"valid ((a,T)# (map ?mapfun \<Gamma>'))" using C by auto
      from False have B:"?G |- TE S x = ((a,T)# (map ?mapfun \<Gamma>'))" by auto
      thus ?thesis using E by auto
    next
      case True
      hence B:"?G |- TE S x = ((a,?op S T)# (map ?mapfun \<Gamma>'))" by auto
      from D have E:"valid ((a,?op S T)# (map ?mapfun \<Gamma>'))" using C by auto
      thus ?thesis using B by auto
    qed
  next
    case (VE x) 
    thus ?case 
    proof -
      let ?op = "replace"
      let ?G = "((a, T) # \<Gamma>')"
      let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op ty.FF ty) else (v,ty)))"
      have C:"valid (map ?mapfun \<Gamma>')" using v2 `valid (\<Gamma>' |- VE x)` by auto
      hence D:"a \<sharp> (map ?mapfun \<Gamma>')" using v2 envop_fresh `valid (\<Gamma>' |- VE x)` by auto
      thus ?case
      proof (cases "a = x")
	case False
	from D have E:"valid ((a,T)# (map ?mapfun \<Gamma>'))" using C by auto
	from False have B:"?G |- VE x = ((a,T)# (map ?mapfun \<Gamma>'))" by auto
	thus ?thesis using E by auto
      next
	case True
	hence B:"?G |- VE x = ((a,?op ty.FF T)# (map ?mapfun \<Gamma>'))" by auto
	from D have E:"valid ((a,?op ty.FF T)# (map ?mapfun \<Gamma>'))" using C by auto
	thus ?thesis using B by auto
      qed
    qed
  qed (auto)
qed

lemma weakening: 
  assumes a: "\<Gamma>1 \<turnstile> t : \<sigma> ; F" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  and d:"valid \<Gamma>1"
  shows "\<Gamma>2 \<turnstile> t:\<sigma> ; F"
using a b c d
proof (nominal_induct \<Gamma>1 t \<sigma> F avoiding: \<Gamma>2 rule: typing.strong_induct)
  case (T_If \<Gamma> t1 T1 F1 t2 T2 F2 t3 T3 F3 T \<Gamma>2)
    have A:"valid (\<Gamma> |+ F1)" using T_If envplus_valid by auto
    have B:"valid (\<Gamma> |- F1)" using T_If envminus_valid by auto
    have A':"valid (\<Gamma>2 |+ F1)" using T_If envplus_valid by auto
    have B':"valid (\<Gamma>2 |- F1)" using T_If envminus_valid by auto
    have C:"(\<Gamma> |+ F1) \<lless> (\<Gamma>2 |+ F1)" using T_If weakening_envplus by auto
    have D:"(\<Gamma> |- F1) \<lless> (\<Gamma>2 |- F1)" using T_If weakening_envminus by auto
    show ?case using T_If A B C D A' B' by blast
qed (auto | atomize)+ 
(* FIXME: before using meta-connectives and the new induction *)
(* method, this was completely automatic *)
(* need weakening lemmas about env+/- *)


lemma "[] \<turnstile> (Lam[x:Top]. (Iff (App (BI NumberP) (Var x)) (App (BI Add1) (Var x)) (Num 12))) : (Top \<rightarrow> ty.Int : latent_eff.NE) ; TT"
  apply (rule T_Abs)
  apply (auto simp add: fresh_def   supp_def perm_fun_def)

  apply (rule T_If)
  apply auto
  apply (rule T_AppPred)
  apply (auto simp add: valid.intros)
  apply (rule T_App)
  apply (rule T_Const)
  defer
  apply ( simp add: valid.intros)
  apply (rule S_Refl)
  apply (rule T_Var)
  apply (simp add: valid.intros)+
  apply (rule S_Refl)
  apply (simp add: valid.intros)+
  
  done


(* inductive cases about typing *)

inductive_cases iff_t_cases : "G \<turnstile> Iff tst thn els : t ; e"
inductive_cases app_bi_cases : "G \<turnstile> App (Const (BI b)) rand : t ; e"
inductive_cases type_arr_case_num: "\<Gamma> \<turnstile> ((Num n)) : (T1 \<rightarrow> T2 : eff) ; eff'"
inductive_cases type_arr_case_bool: "\<Gamma> \<turnstile> ((Bool b)) : (T1 \<rightarrow> T2 : eff) ; eff'"
inductive_cases type_bi_case: "\<Gamma> \<turnstile> ((BI b)) : t ; eff"
inductive_cases type_add1_case: "\<Gamma> \<turnstile> ((BI Add1)) : t ; eff"
inductive_cases bi_typing_cases: "\<Gamma> \<turnstile> (BI b) : t ; eff"
inductive_cases abs_ty_int: "\<Gamma> \<turnstile> (Abs x body t) : ty.Int ; eff'"
inductive_cases abs_ty_bool: "\<Gamma> \<turnstile> (Abs x body t) : BoolTy ; eff'"
inductive_cases const_ty_int: "\<Gamma> \<turnstile> e : ty.Int ; eff'"
inductive_cases const_ty_bool: "\<Gamma> \<turnstile> e : BoolTy ; eff'"
inductive_cases iff_false_ty: "\<Gamma> \<turnstile> Iff (Bool False) thn els : t ; eff"
inductive_cases app_bi_ty: "\<Gamma> \<turnstile> App (BI b) arg : t ; eff"

(* Typing Values*)


lemma false_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> (trm.Bool False) : \<sigma> ; eff \<Longrightarrow> \<sigma> = ty.FF \<and> eff = FF \<and> valid \<Gamma>"
apply (ind_cases "\<Gamma> \<turnstile> (trm.Bool False) : \<sigma> ; eff")
apply (auto simp add: trm.inject)
done

lemma num_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> (Num n) : \<sigma> ; eff \<Longrightarrow> \<sigma> = ty.Int \<and> eff = TT \<and> valid \<Gamma>"
by (ind_cases "\<Gamma> \<turnstile> (Num n) : \<sigma> ; eff") auto

lemma true_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> (trm.Bool True) : \<sigma> ; eff \<Longrightarrow> \<sigma> = ty.TT \<and> eff = TT \<and> valid \<Gamma> "
by (ind_cases "\<Gamma> \<turnstile> (trm.Bool True) : \<sigma> ; eff") 
 (auto simp add: trm.inject)

lemma bool_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> (trm.Bool b) : \<sigma> ; eff \<Longrightarrow>  (\<sigma> = ty.TT \<or> \<sigma> = ty.FF) \<and> valid \<Gamma> "
apply (ind_cases "\<Gamma> \<turnstile> (trm.Bool b) : \<sigma> ; eff")
apply (auto simp add: trm.inject)
done

lemma bi_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> (BI b) : \<sigma> ; eff \<Longrightarrow> eff = TT \<and> \<sigma> = \<Delta>\<^isub>\<tau> b \<and> valid \<Gamma>"
apply (ind_cases "\<Gamma> \<turnstile> (BI b) : \<sigma> ; eff")
apply (auto simp add: trm.inject)
done

inductive_cases bool_sub_int: "\<turnstile> BoolTy <: ty.Int"
inductive_cases tt_sub_int: "\<turnstile> ty.TT <: ty.Int"
inductive_cases ff_sub_int: "\<turnstile> ty.FF <: ty.Int"
thm bool_sub_int
inductive_cases arr_sub_int: "\<turnstile> A\<rightarrow>B:L <: ty.Int"
inductive_cases int_sub_tt: "\<turnstile> ty.Int <: ty.TT"
inductive_cases int_sub_ff: "\<turnstile> ty.Int <: ty.FF"
inductive_cases arr_sub_tt: "\<turnstile> A\<rightarrow>B:L <: ty.TT"
inductive_cases arr_sub_ff: "\<turnstile> A\<rightarrow>B:L <: ty.FF"
inductive_cases int_sub_bool_cases: "\<turnstile> ty.Int <: Union [ty.TT, ty.FF]"
inductive_cases arr_sub_bool_cases: "\<turnstile> A\<rightarrow>B:L <: Union [ty.TT, ty.FF]"

declare BoolTy_def[simp]


lemma int_sub_bool:
  assumes "\<turnstile> ty.Int <: BoolTy"
  shows "P"
  using prems
proof -
  have "\<turnstile> ty.Int <: ty.TT \<or> \<turnstile> ty.Int <: ty.FF" using prems int_sub_bool_cases by auto
  thus ?thesis using int_sub_ff int_sub_tt by auto
qed

lemma arr_sub_bool:
  assumes "\<turnstile> A\<rightarrow>B:L <: BoolTy"
  shows "P"
  using prems
proof -
  have "\<turnstile> A\<rightarrow>B:L <: ty.TT \<or> \<turnstile> A\<rightarrow>B:L <: ty.FF" using prems arr_sub_bool_cases[of A B L] by auto
  thus ?thesis using arr_sub_ff[of A B L] arr_sub_tt[of A B L] by auto
qed

thm int_sub_bool

inductive_cases abs_ty_elim2[consumes 1, case_names 1]: "\<Gamma> \<turnstile> Lam[x:S].b : T ; eff"

lemma int_value:
  assumes a:"v : values"
  and b:"\<Gamma> \<turnstile> v : T ; F"
  and c:"\<turnstile> T <: ty.Int"
  shows "EX n. v = (Num n)"
  using prems
proof (induct rule: values.induct)
  case num_value thus ?case by auto
next
  case (bool_value b)
  hence "T = ty.TT \<or> T = ty.FF" using bool_ty_elim by auto
  thus ?case using bool_value tt_sub_int ff_sub_int by auto
next
  case (abs_value b S x)
  thus ?case using arr_sub_int
    by (induct rule: abs_ty_elim2) auto
next
  case (bi_value b)
  thus ?case using bi_ty_elim[of \<Gamma> b T F] using arr_sub_int by (nominal_induct b rule: builtin.induct) auto
qed

  
lemma bool_value:
  assumes a:"v : values"
  and b:"\<Gamma> \<turnstile> v : T ; F"
  and c:"\<turnstile> T <: BoolTy"
  shows "EX b. v = (Bool b)"
  using prems
proof (induct rule: values.induct)
  case num_value thus ?case using num_ty_elim[of \<Gamma> _ T F] int_sub_bool by auto
next
  case (bool_value b) thus ?case by auto
next
  case (abs_value b S x)
  thus ?case using arr_sub_bool 
    by (induct rule: abs_ty_elim2) auto
next
  case (bi_value b)
  thus ?case using bi_ty_elim[of \<Gamma> b T F] using arr_sub_bool by (nominal_induct b rule: builtin.induct) auto
qed

lemma value_int_ty:
  assumes a:"\<Gamma> \<turnstile> e : ty.Int ; eff"
  and b: "e : values"
  shows "EX n. e = (Num n)"
  using b a int_value[of e _ ty.Int] by auto

lemma value_bool_ty:
  assumes a:"\<Gamma> \<turnstile> e : BoolTy ; eff"
  and b: "e : values"
  shows "EX b. e = (Bool b)"
  using b a bool_value[OF b a] by auto

lemma typing_bi:
  assumes a:"\<Gamma> \<turnstile> (BI b) : t ; eff"
  shows "t = \<Delta>\<^isub>\<tau> b"
  using a bi_typing_cases[of \<Gamma> b t eff "t = \<Delta>\<^isub>\<tau> b"]
  by (simp add: trm.inject)  

inductive_cases arr_sub_arr_cases:"\<turnstile> A1 \<rightarrow> A2 : L <: B1 \<rightarrow> B2 : L'"

lemma typed_prim_reduce:
  assumes a:"\<Gamma> \<turnstile> (BI b) : U ; eff" and b:"\<Gamma> \<turnstile> v : T ; eff'" and c:"v : values"
  and sub:"\<turnstile> T <: T0" and d: "\<turnstile> U <:  T0 \<rightarrow> T1 : le" 
  shows "EX v'. \<Delta> b v = Some v'"
  using a b c d sub
  proof (nominal_induct b rule: builtin.induct)
    case Add1
    have "U = \<Delta>\<^isub>\<tau> Add1" using Add1 typing_bi[of \<Gamma> Add1 "U" eff] by simp
    hence "U = ty.Int \<rightarrow> ty.Int : latent_eff.NE" by auto
    hence "\<turnstile> T <: ty.Int " and "le = latent_eff.NE" using sub d arr_sub_arr_cases[of ty.Int ty.Int latent_eff.NE T0 T1 le] 
      by auto
    hence "EX n. v = (Num n)" using c b int_value by auto
    then obtain n where "v = (Num n)" by auto
    thus ?case by (auto simp add: \<Delta>.simps)
  next
    case Nott show ?case using `v : values` Nott
      by (induct v rule: values.induct)  auto
  next
    case NumberP thus ?case by auto
  next
    case BooleanP thus ?case by auto
  next
    case ProcP thus ?case by auto
  qed


text {* Progress together with necessary lemmas *}

(* first some lemmas about decomposing various kinds of syntax *)

lemma if_decomp:
  assumes b:"closed tst \<Longrightarrow> (\<exists>E L R. tst = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> tst : values"
  and c:"closed (Iff tst thn els)"
  shows "(EX E L R. (Iff tst thn els) = E L \<and> E : ctxt \<and> L \<hookrightarrow> R) \<or> (Iff tst thn els) : values"
  proof -
    {
      assume "tst : values"
      hence "EX E L R. Iff tst thn els = E L \<and> E : ctxt \<and> (L \<hookrightarrow> R)"
        using if_val_reduces[of tst thn els] ex_help[of "Iff tst thn els" "(%t. t)"] by auto
    }
    moreover
    {
      assume asm:"~ tst : values"
      have cl:"closed tst" using `closed (Iff tst thn els)` by (auto simp add: closed_def trm.supp)
      hence ih:"\<exists>E t t'. tst = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'" using b asm by auto
      hence "\<exists>E t t' . Iff tst thn els = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
        using reduce_in_ctxt[of "(%t . (Iff t thn els))"] ih by auto
    }
    ultimately show ?thesis by auto
  qed
  

inductive_cases tt_sub_arr_cases: "\<turnstile> ty.TT <:A1 \<rightarrow> A2 : L"
inductive_cases ff_sub_arr_cases: "\<turnstile> ty.FF <:A1 \<rightarrow> A2 : L"
inductive_cases num_sub_arr_cases: "\<turnstile> ty.Int <:A1 \<rightarrow> A2 : L"

lemma app_decomp:
  assumes a:" G \<turnstile> rator : U ; eff1"
  and a':"\<turnstile> U <: T0 \<rightarrow> T1 : le"
  and aa:" G \<turnstile> rand : T ; eff"
  and b:"closed rator \<Longrightarrow> (\<exists>E L R. rator = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> rator \<in> values"
  and bb:"closed rand \<Longrightarrow> (\<exists>E L R. rand = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> rand \<in> values"
  and c:"closed (App rator rand)"
  and sub:"\<turnstile> T <: T0"
  shows "(EX E L R. (App rator rand) = E L \<and> E : ctxt \<and> L \<hookrightarrow> R) \<or> (App rator rand) : values"
  proof -
    have well_typed:"G \<turnstile> (App rator rand) : T1 ; eff.NE"
      using T_App[of G rator U eff1 T0 T1 le rand T eff] a a' aa sub by auto
    have "closed rator" using c by (auto simp add: closed_def trm.supp)
    hence ih1:"(\<exists>E L R. rator = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> rator \<in> values" using b by simp
    have "closed rand" using c by (auto simp add: closed_def trm.supp)
    hence ih2:"(\<exists>E L R. rand = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> rand \<in> values" using bb by simp
    {
      assume asm1:"rator \<in> values" and asm2:"rand \<in> values"
      hence "(EX E L R. (App rator rand) = E L \<and> E : ctxt \<and> L \<hookrightarrow> R)" using asm1 a aa a' sub well_typed
        proof (nominal_induct avoiding: rand rule: values.strong_induct )
          case (abs_value x t b)
          let ?E = "(%t. t)"
          let ?L = "App (Abs x b t) rand"
          have "?L \<hookrightarrow> (b[x::=rand])" by (rule e_beta)
          thus ?case using ex_help[of ?L ?E ?L] by auto
        next
          case (bool_value b)
	  hence "U = ty.TT \<or> U = ty.FF" using true_ty_elim false_ty_elim by (cases b) auto
	  thus ?case using tt_sub_arr_cases[of T0 T1 le] ff_sub_arr_cases[of T0 T1 le] `\<turnstile> U <: T0 \<rightarrow> T1 : le` by blast
        next
          case (num_value b)
	  hence "U = ty.Int" using num_ty_elim by auto
	  thus ?case using num_sub_arr_cases[of T0 T1 le] num_value by auto
        next
          case (bi_value b) 
          let ?E = "(%t. t)"
          let ?L = "App ((BI b)) rand"
          have h:"\<And>v. (\<Delta> b rand) = (Some v)  \<Longrightarrow> App ((BI b)) rand \<hookrightarrow> v" using bi_value by auto
          have "EX v . (\<Delta> b rand) = (Some v)" using bi_value typed_prim_reduce[of G b U]  by auto
          then obtain v' where "(\<Delta> b rand) = (Some v')" by auto
          then show ?case using h[of v'] ex_help[of ?L ?E] by auto
        qed
    }
    moreover
    {
      assume asm1:"rator \<in> values" and asm2:"rand \<notin> values"
      have "\<exists>E t t' . App rator rand = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
	using asm1 asm2 reduce_in_ctxt[of "(%t . (App rator t))"] ih2 by auto
    }
    moreover
    {
      assume asm:"rator \<notin> values"
      have "\<exists>E t t' . App rator rand = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
	using asm reduce_in_ctxt[of "(%t . (App t rand))"] ih1 by auto
    }  
    ultimately show ?thesis by auto
  qed


(* then the main lemma, that every well typed term can be decomposed
   into a context and a redex *)

lemma decomposition:
  assumes a:"closed e" and b:"\<Gamma> \<turnstile> e : t ; eff"
  shows "(EX E L R. e = E L \<and> E : ctxt \<and> L \<hookrightarrow> R) \<or> e : values"
  using b a
proof (induct rule: typing.induct)
  case T_Var
  thus ?case using closed_def by (auto simp add: at_supp at_name_inst trm.supp) 
next
  case T_If
  thus ?case using if_decomp by auto
next
  case T_IfTrue
  thus ?case using if_decomp by auto
next
  case T_IfFalse
  thus ?case using if_decomp by auto
next
  case T_App
  thus ?case using app_decomp by auto
next
  case T_AppPred
  thus ?case using app_decomp by auto
next
  case T_AppPredTrue
  thus ?case using app_decomp by auto
next
  case T_AppPredFalse
  thus ?case using app_decomp by auto
qed (simp_all) (* The value cases are automatic *)

(* Now we conclude progress *)

theorem progress:
  assumes typed:"\<Gamma> \<turnstile> e : t ; eff" and cl:"closed e"
  shows "e : values \<or> (EX e'. e \<longrightarrow> e')"
proof (cases "e : values")
  case False
  hence "(\<exists>E L R. e = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R)" using decomposition[OF cl typed] by auto
  thus ?thesis by auto
qed (simp)

(* Some useful lemmas for deriving facts from typing derivations *)

inductive_cases app_ty_elim2[consumes 1, case_names 1 2 3 4]: "\<Gamma> \<turnstile> App t1 t2 : \<sigma> ; eff"
thm app_ty_elim2
inductive_cases iff_ty_elim2[consumes 1, case_names 1 2 3]: "\<Gamma> \<turnstile> Iff t1 t2 t3 : T ; eff"
thm abs_ty_elim2

(* slow *)
lemma app_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> App t1 t2 : \<sigma> ; eff \<Longrightarrow> 
  \<exists> T0 T0' T1 le eff' eff'' U. (\<Gamma> \<turnstile> t1 : U ; eff' \<and> \<Gamma> \<turnstile> t2 : T0' ; eff'' \<and> \<turnstile> U <: T0 \<rightarrow> T1 : le \<and> \<turnstile> T0' <: T0 \<and> T1 = \<sigma>)"
  apply (ind_cases "\<Gamma> \<turnstile> App t1 t2 : \<sigma> ; eff")
  apply (auto simp add: trm.inject ty.inject)
  by metis+

lemma abs_ty_elim_eff[rule_format]: 
  "\<lbrakk>\<Gamma> \<turnstile> Lam[a:T0].b : \<sigma> ; eff\<rbrakk> \<Longrightarrow> eff = eff.TT"
  by (ind_cases "\<Gamma> \<turnstile> Lam[a:T0].b : \<sigma> ; eff")
     (auto simp add: trm.inject)


lemma abs_ty_elim[rule_format]: 
  "\<lbrakk>\<Gamma> \<turnstile> Lam[a:T0].b : \<sigma> ; eff ; a \<sharp> \<Gamma>\<rbrakk> \<Longrightarrow> 
  \<exists> T1 eff' L S. ((a,T0)#\<Gamma> \<turnstile> b : T1 ; eff' \<and> \<sigma> = (T0 \<rightarrow> T1 : L) \<and> eff = eff.TT \<and> ((eff' = TE S a \<and> L = Latent S) \<or> L = latent_eff.NE))"
apply (ind_cases "\<Gamma> \<turnstile> Lam[a:T0].b: \<sigma> ; eff")
apply(auto simp add: trm.distinct trm.inject alpha) 
apply(drule_tac pi="[(a,x)]::name prm" in typing.eqvt)
apply(auto)
apply(subgoal_tac "([(a,x)]::name prm)\<bullet>\<Gamma> = \<Gamma>")(*A*)
apply(force simp add: calc_atm)
(*A*)
apply(force intro!: pt_fresh_fresh[OF pt_name_inst, OF at_name_inst])

apply(drule_tac pi="[(a,x)]::name prm" in typing.eqvt)
apply(auto)
apply(subgoal_tac "([(a,x)]::name prm)\<bullet>\<Gamma> = \<Gamma>")(*A*)
apply(force simp add: calc_atm)
(*A*)
apply(force intro!: pt_fresh_fresh[OF pt_name_inst, OF at_name_inst])
done

inductive_cases abs_ty_cases[consumes 1, case_names 1 2]:"\<Gamma> \<turnstile> Lam[a:T0].b: \<sigma> ; eff"
thm abs_ty_cases

(*
lemma app_abs_ty_elim_eff[rule_format]: 
  "\<lbrakk>\<Gamma> \<turnstile> App (Abs x b T) t2 : \<sigma> ; eff ; x \<sharp> \<Gamma>\<rbrakk> \<Longrightarrow> eff = eff.NE"
  proof (ind_cases "\<Gamma> \<turnstile> App (Abs x b T) t2 : \<sigma> ; eff", auto simp add: trm.inject abs_ty_elim)
    fix T0 S eff1 U 
    assume "\<Gamma> \<turnstile> Lam [x:T].b : U ; eff1 "" \<turnstile> U <: T0 \<rightarrow> \<sigma> : Latent S" "x \<sharp> \<Gamma>"
    then obtain T1 L where "U = T \<rightarrow> T1 : L" using abs_ty_elim[of \<Gamma> x b T "U" L] by auto
    thus False using prems arr_sub_arr_cases[of T _ latent_eff.NE T0 \<sigma> "Latent S"] by (auto simp add: ty.inject)
  next
    fix T0 S eff1 U
    assume "\<Gamma> \<turnstile> Lam [x:T].b : U ; eff1 "" \<turnstile> U <: T0 \<rightarrow> \<sigma> : Latent S" "x \<sharp> \<Gamma>"
    then obtain T1 where "U = T \<rightarrow> T1 : latent_eff.NE" using abs_ty_elim[of \<Gamma> x b T "U"] by auto
    thus False using prems arr_sub_arr_cases[of T _ latent_eff.NE T0 \<sigma> "Latent S"] by (auto simp add: ty.inject)
  next
    fix T0 S eff1 U
    assume "\<Gamma> \<turnstile> Lam [x:T].b : U ; eff1 "" \<turnstile> U <: T0 \<rightarrow> \<sigma> : Latent S" "x \<sharp> \<Gamma>"
    then obtain T1 where "U = T \<rightarrow> T1 : latent_eff.NE" using abs_ty_elim[of \<Gamma> x b T "U"] by auto
    thus False using prems arr_sub_arr_cases[of T _ latent_eff.NE T0 \<sigma> "Latent S"] by (auto simp add: ty.inject)
  qed

*)
lemma if_ty_elim_weak[rule_format]: 
  "\<Gamma> \<turnstile> Iff t1 t2 t3: \<sigma> ; eff \<Longrightarrow> \<exists> T0 eff'. (\<Gamma> \<turnstile> t1 : T0 ; eff') \<and> eff = NE"
by (ind_cases "\<Gamma> \<turnstile> Iff t1 t2 t3: \<sigma> ; eff")
   (auto simp add: trm.inject)

lemma if_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> Iff t1 t2 t3: \<sigma> ; eff \<Longrightarrow> 
  (\<exists> T1 T2 T3 F1 F2 F3. (\<Gamma> \<turnstile> t1 : T1 ; F1) \<and> \<Gamma> |+ F1 \<turnstile> t2 : T2 ; F2 \<and> \<Gamma> |- F1 \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T2 <: \<sigma>  \<and> \<turnstile> T3 <: \<sigma> \<and> eff = NE)
  \<or>
  (\<exists> T1 T3 F3. (\<Gamma> \<turnstile> t1 : T1 ; FF) \<and> \<Gamma> \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T3 <: \<sigma> \<and> eff = NE)
  \<or>
  (\<exists> T1 T2 F2. (\<Gamma> \<turnstile> t1 : T1 ; TT) \<and> \<Gamma> \<turnstile> t2 : T2 ; F2 \<and> \<turnstile> T2 <: \<sigma>  \<and> eff = NE)"
proof (ind_cases "\<Gamma> \<turnstile> Iff t1 t2 t3: \<sigma> ; eff")
  fix e1 T1 eff1 e2 T2 eff2 e3 T3 eff3
  assume "Iff t1 t2 t3 = Iff e1 e2 e3"" eff = eff.NE""  \<Gamma> \<turnstile> e1 : T1 ; eff1""  env_plus eff1 \<Gamma> \<turnstile> e2 : T2 ; eff2 "
    "env_minus eff1 \<Gamma> \<turnstile> e3 : T3 ; eff3"" \<turnstile> T2 <: \<sigma>"" \<turnstile> T3 <: \<sigma>"
  hence A:"t1 = e1" "t2 = e2" "t3 = e3" using trm.inject by auto
  thus ?thesis using prems by blast 
next
  fix e1 T1 e2 T2 effa e3
  assume "Iff t1 t2 t3 = Iff e1 e2 e3"" eff = eff.NE""  \<Gamma> \<turnstile> e1 : T1 ; TT ""  \<Gamma> \<turnstile> e2 : T2 ; effa "" \<turnstile> T2 <: \<sigma>"
  thus ?thesis by (auto simp add: trm.inject)
next
  fix e1 T1 e2 T3 effa e3
  assume "Iff t1 t2 t3 = Iff e1 e2 e3"" eff = eff.NE""  \<Gamma> \<turnstile> e1 : T1 ; FF ""  \<Gamma> \<turnstile> e3 : T3 ; effa "" \<turnstile> T3 <: \<sigma>"
  thus ?thesis by (auto simp add: trm.inject)
qed

inductive_cases iff_false_ty_cases:  "\<Gamma> \<turnstile> Iff (trm.Bool False) t2 t3: \<sigma> ; eff"
inductive_cases ff_eff_cases: "\<Gamma> \<turnstile> e : T; FF"
inductive_cases tt_eff_cases: "\<Gamma> \<turnstile> e : T; TT"
inductive_cases ne_eff_cases: "\<Gamma> \<turnstile> e : T; NE"


lemma if_true_ty_elim[rule_format]: 
   "\<lbrakk>\<Gamma> \<turnstile> Iff v t2 t3: \<sigma> ; eff ; v : values; v ~= Bool False\<rbrakk> \<Longrightarrow>
  \<exists> T0 eff'. ((\<Gamma> \<turnstile> t2 : T0 ; eff') \<and> \<turnstile> T0 <: \<sigma> \<and> eff = NE)"  
proof (ind_cases "\<Gamma> \<turnstile> Iff (v) t2 t3: \<sigma> ; eff")
  fix eff1 eff2 T1 T2 e1 e2 e3 
  assume "v : values" "env_plus eff1 \<Gamma> \<turnstile> e2 : T2 ; eff2" "Iff v t2 t3 = Iff e1 e2 e3" "\<turnstile> T2 <: \<sigma>" 
    "\<Gamma> \<turnstile> e1 : T1 ; eff1" "eff = NE"
  have "\<Gamma> \<turnstile> v : T1 ; eff1" using prems by (simp add: trm.inject)
  have "eff1 = eff.NE \<or> eff1 = FF \<or> eff1 = TT" using `v : values` `\<Gamma> \<turnstile> v : T1 ; eff1`
  proof (induct rule: values.induct)
    case (abs_value b T x) thus ?case using abs_value abs_ty_elim_eff by auto
  next
    case (num_value n) thus ?case using num_ty_elim by auto
  next
    case (bool_value n) thus ?case using false_ty_elim true_ty_elim by (cases n) auto
  next
    case bi_value thus ?case using bi_ty_elim by auto
  qed
  hence "env_plus eff1 \<Gamma> = \<Gamma>" by auto
  hence "\<Gamma> \<turnstile> e2 : T2 ; eff2 \<and> \<turnstile> T2 <: \<sigma>" using prems by auto
  thus ?thesis using prems by (auto simp add: trm.inject)
next
  fix e1 T2 e2 e3 effa
  assume "Iff v t2 t3 = Iff e1 e2 e3"  "\<Gamma> \<turnstile> e2 : T2 ; effa"  "\<turnstile> T2 <: \<sigma>" "eff = NE"
  thus ?thesis by (auto simp add: trm.inject)
next
  fix e1 T1 e3 T3 effa e2
  assume "v : values" "v \<noteq> trm.Bool False" "Iff v t2 t3 = Iff e1 e2 e3" "\<Gamma> \<turnstile> e1 : T1 ; FF" "eff = NE"
  have "v = e1" using prems trm.inject by auto
  hence tv:"\<Gamma> \<turnstile> v : T1 ; FF" by simp
  have "v = Bool False" using `v : values` tv
  proof (induct v rule: values.induct)
    case (abs_value x T b) thus ?case using abs_ty_elim_eff[of \<Gamma> x b T T1 FF] by auto
  next
    case (num_value n) thus ?case using num_ty_elim[of _ _ _ FF] by auto
  next
    case (bool_value n) thus ?case using true_ty_elim[of _ _ FF] by (cases n) auto
  next
    case bi_value thus ?case using bi_ty_elim[of _ _ _ FF] by auto
  qed
  show ?thesis using `v = Bool False` `v ~= Bool False` by auto
qed 


lemma if_false_ty_elim[rule_format]: 
   "\<Gamma> \<turnstile> Iff (trm.Bool False) t2 t3: \<sigma> ; eff \<Longrightarrow>
  \<exists> T0 eff'. ((\<Gamma> \<turnstile> t3 : T0 ; eff') \<and> \<turnstile> T0 <: \<sigma> \<and> eff = eff.NE)"  
proof (ind_cases "\<Gamma> \<turnstile> Iff (trm.Bool False) t2 t3: \<sigma> ; eff")
  fix e1 e2 e3 T1
  assume "Iff (trm.Bool False) t2 t3 = Iff e1 e2 e3" and "\<Gamma> \<turnstile> e1 : T1 ; TT"
  hence "\<Gamma> \<turnstile> (trm.Bool False) : T1 ; TT" by (simp add: trm.inject)
  hence "TT = FF" using false_ty_elim[of \<Gamma> T1 TT] by simp
  thus ?thesis by (simp)
next
  fix e1 e2 e3 T1 T3 effa
  assume "Iff (trm.Bool False) t2 t3 = Iff e1 e2 e3" and " eff = eff.NE"and" \<Gamma> \<turnstile> e1 : T1 ; FF" and "  \<Gamma> \<turnstile> e3 : T3 ; effa"and " \<turnstile> T3 <: \<sigma>"
  thus ?thesis by (auto simp add: trm.inject)
next
  fix e1 e2 e3 T1 T3 eff1 eff3
  assume "Iff (trm.Bool False) t2 t3 = Iff e1 e2 e3" and "eff = eff.NE" 
    and f:"\<Gamma> \<turnstile> e1 : T1 ; eff1" and g:"env_minus eff1 \<Gamma> \<turnstile> e3 : T3 ; eff3" and "\<turnstile> T3 <: \<sigma>"
  hence "e1 = Bool False" and "t3 = e3" by (auto simp add: trm.inject)
  hence "eff1 = FF" using f false_ty_elim by auto
  hence "env_minus eff1 \<Gamma> = \<Gamma>" by simp
  hence "\<Gamma> \<turnstile> e3 : T3 ; eff3" using g by simp
  thus ?thesis using `t3 = e3` `\<turnstile> T3 <: \<sigma>` `eff = eff.NE` by auto
qed 

lemma var_ty_elim:
  "\<Gamma> \<turnstile> Var v : \<sigma> ; eff \<Longrightarrow> (v,\<sigma>) : set \<Gamma> \<and> eff = VE v \<and> valid \<Gamma>"
  by (ind_cases "\<Gamma> \<turnstile> Var v : \<sigma> ; eff")
     (auto simp add: trm.inject)

inductive_cases app_ty_ff:"\<Gamma> \<turnstile> App e arg : T' ; FF"
  
lemma app_ty_ff_elim:
  "\<Gamma> \<turnstile> App rator rand : T ; FF \<Longrightarrow>
  EX S T0 le F1 T0' F2 U.  \<Gamma> \<turnstile> rator : U ; F1 \<and> \<Gamma> \<turnstile> rand : T0' ; F2 \<and> \<turnstile> T0' <: T0 \<and> \<turnstile> U <: T0 \<rightarrow> T : le \<and>
  le = Latent S \<and> (~ (\<turnstile> T0' <: S)) \<and> rand : values \<and> closed rand"
  proof (ind_cases "\<Gamma> \<turnstile> App rator rand : T ; FF")
    fix e1 T0 S eff1 e2 Ta eff2 U
    assume "App rator rand = App e1 e2 "" \<Gamma> \<turnstile> e1 : U ; eff1 " "\<turnstile> U <:  T0 \<rightarrow> T : Latent S"
      "\<Gamma> \<turnstile> e2 : Ta ; eff2 ""\<turnstile> Ta <: T0""~ (\<turnstile> Ta <: S)" "e2 : values" "closed e2"
    have a:" \<Gamma> \<turnstile> rator : U ; eff1 " using prems trm.inject by auto
    have b:"\<Gamma> \<turnstile> rand : Ta ; eff2"  using prems trm.inject by auto
    have c:"rand : values" "closed rand" using prems trm.inject by auto
    from a b c prems show ?thesis by blast
  qed
  
lemma app_ty_tt_elim:
  "\<Gamma> \<turnstile> App rator rand : T ; TT \<Longrightarrow>
  EX S T0 le F1 T0' F2 U. \<Gamma> \<turnstile> rator : U ; F1 \<and> \<Gamma> \<turnstile> rand : T0' ; F2 \<and> \<turnstile> T0' <: T0 \<and> \<turnstile> U <: T0 \<rightarrow> T : le 
  \<and> le = Latent S \<and> \<turnstile> T0' <: S "
  proof (ind_cases "\<Gamma> \<turnstile> App rator rand : T ; TT")
    fix e1 T0 S eff1 e2 Ta eff2 U
    assume "App rator rand = App e1 e2 "" \<Gamma> \<turnstile> e1 : U ; eff1 " "\<turnstile> U <: T0 \<rightarrow> T : Latent S"
      "\<Gamma> \<turnstile> e2 : Ta ; eff2 ""\<turnstile> Ta <: T0"" \<turnstile> Ta <: S"
    have a:" \<Gamma> \<turnstile> rator : U ; eff1 " using prems trm.inject by auto
    have b:"\<Gamma> \<turnstile> rand : Ta ; eff2"  using prems trm.inject by auto
    from a b prems show ?thesis by blast
  qed

text {* values don't have union types *}

lemma value_simple_type:
  assumes A:"\<Gamma> \<turnstile> v : T ; F" and B:"v : values"
  shows "simple_ty T"
using B A
proof (nominal_induct v avoiding: \<Gamma> rule: values.strong_induct)
  case (bi_value b) thus ?case using bi_ty_elim[of \<Gamma> b T F]
    by (nominal_induct b rule: builtin.induct)  
       (auto simp add: trm.inject)
next
  case num_value thus ?case using num_ty_elim[OF num_value] by auto
next
  case bool_value thus ?case using bool_ty_elim[OF bool_value] by auto
next
  case (abs_value a T' b \<Gamma>') thus ?case using abs_ty_elim[of \<Gamma>' a b T' T F] by auto
qed

text {* lemmas about the effects of closed terms *}

lemma ve_not_closed:
  "\<Gamma> \<turnstile> e : T ; eff.VE x \<Longrightarrow>
  x : supp e"
  by (ind_cases "\<Gamma> \<turnstile> e : T ; eff.VE x")
     (auto simp add: eff.inject trm.supp at_supp supp_atm)

lemma te_not_closed:
  "\<Gamma> \<turnstile> e : T ; eff.TE T' x \<Longrightarrow>
  x : supp e"
  proof (ind_cases "\<Gamma> \<turnstile> e : T ; eff.TE T' x")
    fix e1 T0 S eff1 e2 Ta xa
    assume "e = App e1 e2" "TE T' x = TE S xa" "\<Gamma> \<turnstile> e2 : Ta ; VE xa"
    have "x = xa" using prems eff.inject by auto
    hence "\<Gamma> \<turnstile> e2 : Ta ; VE x" using prems eff.inject by auto
    hence "x : supp e2" using ve_not_closed by auto
    thus "x : supp e" using prems trm.supp by auto
  qed

lemma closed_eff:
  assumes "closed e" and "\<Gamma> \<turnstile> e : T ; eff"
  shows "simple_eff eff"
using prems
proof (nominal_induct eff rule: eff.induct)
  case (VE name) thus ?case using ve_not_closed[of _ e _ name] closed_def by auto
next
  case (TE _ name) thus ?case using te_not_closed[of _ e _ _ name] closed_def by auto
qed (auto)

lemma closed_eff_below_NE:
  assumes "closed e" and "\<Gamma> \<turnstile> e : T ; eff"
  shows "\<turnstile> eff <e: eff.NE"
  using closed_eff simple_eff_below_ne prems by auto

inductive_cases const_ty_int_case: "\<Gamma> \<turnstile> (Num n) : ty.Int ; eff"
inductive_cases trm_ty_int_case: "\<Gamma> \<turnstile> e : ty.Int ; eff"
inductive_cases const_ty_bool_case: "\<Gamma> \<turnstile> (Bool b) : BoolTy ; eff"

lemma add1_eff_ne:
  "\<Gamma> \<turnstile> (App (BI Add1) v) :  T1 ; eff1 \<Longrightarrow> eff1 = eff.NE"
proof (ind_cases " \<Gamma> \<turnstile> (App (BI Add1) v) :  T1 ; eff1")
  assume "eff1 = eff.NE" thus ?thesis by simp
next
  fix T0 T1 S eff1a e1 e2 U
  assume "\<Gamma> \<turnstile> e1 : U ; eff1a" "App (BI Add1) v = App e1 e2" "\<turnstile> U <: T0 \<rightarrow> T1 : Latent S"
  hence "\<Gamma> \<turnstile> (BI Add1) : U ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Add1 = U" using type_add1_case[of \<Gamma> "U"] by (auto simp add: trm.inject)
  hence "\<dots> = ty.Int \<rightarrow> ty.Int : latent_eff.NE" by auto
  thus ?thesis using prems arr_sub_arr_cases[of ty.Int ty.Int latent_eff.NE] by (auto simp add: ty.inject)
next
  fix T0 T1 S eff1a e1 e2 U
  assume "\<Gamma> \<turnstile> e1 : U ; eff1a" "App (BI Add1) v = App e1 e2" "\<turnstile> U <: T0 \<rightarrow> T1 : Latent S"
  hence "\<Gamma> \<turnstile> (BI Add1) : U ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Add1 = U" using type_add1_case[of \<Gamma> "U"] by (auto simp add: trm.inject)
  hence "\<dots> = ty.Int \<rightarrow> ty.Int : latent_eff.NE" by auto
  thus ?thesis using prems arr_sub_arr_cases[of ty.Int ty.Int latent_eff.NE] by (auto simp add: ty.inject)
next
  fix T0 T1 S eff1a e1 e2 U
  assume "\<Gamma> \<turnstile> e1 : U ; eff1a" "App (BI Add1) v = App e1 e2" "\<turnstile> U <: T0 \<rightarrow> T1 : Latent S"
  hence "\<Gamma> \<turnstile> (BI Add1) : U ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Add1 = U" using type_add1_case[of \<Gamma> "U"] by (auto simp add: trm.inject)
  hence "\<dots> = ty.Int \<rightarrow> ty.Int : latent_eff.NE" by auto
  thus ?thesis using prems arr_sub_arr_cases[of ty.Int ty.Int latent_eff.NE] by (auto simp add: ty.inject)
qed

inductive_cases type_nott_case: "\<Gamma> \<turnstile> (BI Nott) : t ; e"

lemma nott_eff_ne:
  "\<Gamma> \<turnstile> (App (BI Nott) v) :  T1 ; eff1 \<Longrightarrow> eff1 = eff.NE"
proof (ind_cases " \<Gamma> \<turnstile> (App (BI Nott) v) :  T1 ; eff1")
  assume "eff1 = eff.NE" thus ?thesis by simp
next
  fix T0 T1 S eff1a e1 e2 U
  assume "\<Gamma> \<turnstile> e1 : U ; eff1a" "App (BI Nott) v = App e1 e2" "\<turnstile> U <: T0 \<rightarrow> T1 : Latent S"
  hence "\<Gamma> \<turnstile> (BI Nott) : U ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Nott = U" using type_nott_case[of \<Gamma> "U"] by (auto simp add: trm.inject)
  hence "\<dots> = Top \<rightarrow> BoolTy : latent_eff.NE" by auto
  thus ?thesis using prems arr_sub_arr_cases[of Top BoolTy latent_eff.NE] by (auto simp add: ty.inject)
next
  fix T0 T1 S eff1a e1 e2 U
  assume "\<Gamma> \<turnstile> e1 : U ; eff1a" "App (BI Nott) v = App e1 e2" "\<turnstile> U <: T0 \<rightarrow> T1 : Latent S"
  hence "\<Gamma> \<turnstile> (BI Nott) : U ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Nott = U" using type_nott_case[of \<Gamma> "U"] by (auto simp add: trm.inject)
  hence "\<dots> = Top \<rightarrow> BoolTy : latent_eff.NE" by auto
  thus ?thesis using prems arr_sub_arr_cases[of Top BoolTy latent_eff.NE] by (auto simp add: ty.inject)
next
  fix T0 T1 S eff1a e1 e2 U
  assume "\<Gamma> \<turnstile> e1 : U ; eff1a" "App (BI Nott) v = App e1 e2" "\<turnstile> U <: T0 \<rightarrow> T1 : Latent S"
  hence "\<Gamma> \<turnstile> (BI Nott) : U ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Nott = U" using type_nott_case[of \<Gamma> "U"] by (auto simp add: trm.inject)
  hence "\<dots> = Top \<rightarrow> BoolTy : latent_eff.NE" by auto
  thus ?thesis using prems arr_sub_arr_cases[of Top BoolTy latent_eff.NE] by (auto simp add: ty.inject)
qed

inductive_cases type_booleanp_case: "\<Gamma> \<turnstile> (BI BooleanP) : t ; e"

lemma value_eff:
  assumes "v : values" and "\<Gamma> \<turnstile> v :  T ; eff"
  shows "simple_eff eff"
  using prems
  proof (induct v rule :values.induct)
    case abs_value thus ?case using abs_ty_elim_eff by auto
  next
    case num_value thus ?case using num_ty_elim by auto
  next
    case (bool_value b) thus ?case using true_ty_elim false_ty_elim by (cases b) auto
  next
    case bi_value thus ?case using bi_ty_elim by auto
  qed

lemma booleanp_eff_simple:
  "\<lbrakk>\<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; eff1 ; v : values\<rbrakk> \<Longrightarrow> simple_eff eff1"
proof (ind_cases " \<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; eff1")
  fix T0 T1 S eff1a e1 e2 xa T
  assume "\<Gamma> \<turnstile> e2 : T ; VE xa" "App (BI BooleanP) v = App e1 e2" "v : values"
  hence "VE xa = eff.NE \<or> VE xa = eff.TT  \<or> VE xa = eff.FF " using value_eff[of v \<Gamma> T "VE xa"] 
    by (auto simp add: trm.inject)
  thus ?thesis using ty.distinct by auto
qed (auto)

lemma numberp_eff_simple:
  "\<lbrakk>\<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; eff1 ; v : values\<rbrakk> \<Longrightarrow> simple_eff eff1"
proof (ind_cases " \<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; eff1")
  fix T0 T1 S eff1a e1 e2 xa T
  assume "\<Gamma> \<turnstile> e2 : T ; VE xa" "App (BI NumberP) v = App e1 e2" "v : values"
  hence "VE xa = eff.NE \<or> VE xa = eff.TT  \<or> VE xa = eff.FF " using value_eff[of v \<Gamma> T "VE xa"]
    by (auto simp add: trm.inject)
  thus ?thesis using ty.distinct by auto
qed (auto)

lemma procp_eff_simple:
  "\<lbrakk>\<Gamma> \<turnstile> (App (BI ProcP) v) :  T1 ; eff1 ; v : values\<rbrakk> \<Longrightarrow> simple_eff eff1"
proof (ind_cases " \<Gamma> \<turnstile> (App (BI ProcP) v) :  T1 ; eff1")
  fix T0 T1 S eff1a e1 e2 xa T
  assume "\<Gamma> \<turnstile> e2 : T ; VE xa" "App (BI ProcP) v = App e1 e2" "v : values"
  hence "VE xa = eff.NE \<or> VE xa = eff.TT  \<or> VE xa = eff.FF " using value_eff[of v \<Gamma> T "VE xa"]
    by (auto simp add: trm.inject)
  thus ?thesis using ty.distinct by auto
qed (auto)


inductive_cases app_boolp_ff: "\<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; FF"

lemma booleanp_FF_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; FF" and "v : values" and "\<Delta> BooleanP v = Some u"
  shows "u = Bool False"
  using `v : values` prems
  proof (induct v rule: values.induct)
    case (bool_value b)
    let ?P = "\<Gamma> \<turnstile> App (BI BooleanP) (trm.Bool b) : T1 ; FF" 
    have "?P ==> ?case"
      proof (ind_cases ?P)
        fix S T e1 e2 T0 eff1 eff2 U
        assume "App (BI BooleanP) (trm.Bool b) = App e1 e2"  "\<Gamma> \<turnstile> e1 : U ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
          "~ (\<turnstile> T <: S)" "e2 : values" "\<turnstile> U <:  T0 \<rightarrow> T1 : Latent S"
        hence a:"\<Gamma> \<turnstile> (BI BooleanP) : U ; eff1 " using trm.inject by auto
        from prems have b:"\<Gamma> \<turnstile> Bool b : T ; eff2" using trm.inject by auto
	have "U = Top \<rightarrow> BoolTy : Latent BoolTy" using a bi_ty_elim[of \<Gamma> BooleanP "U"] by auto
	hence c:"S = BoolTy" using prems arr_sub_arr_cases[of Top BoolTy _ T0 T1 "Latent S"] latent_eff.inject by auto
        from b have d:"T = ty.TT \<or> T = ty.FF" using true_ty_elim false_ty_elim by (cases b) auto
        from c d have "\<turnstile> T <: S" by auto
        thus ?thesis using prems by auto
      qed
    thus ?case using bool_value by auto
  qed (auto)

lemma typing_valid:
  assumes "\<Gamma> \<turnstile> e : T ; F"
  shows "valid \<Gamma>"
using prems 
proof (induct)
  case (T_Abs a \<Gamma> T b T' F') thus ?case using valid_elim[of a T \<Gamma>] by auto
next
  case (T_AbsPred a \<Gamma> T b T' F') thus ?case using valid_elim[of a T \<Gamma>] by auto
qed (auto)


lemma booleanp_TT_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; TT" and "v : values" and "\<Delta> BooleanP v = Some u"
  shows "u = Bool True"
  proof -
    note app_ty_tt_elim[of \<Gamma> "(BI BooleanP)" v T1]
    then obtain A1 U T0 T1 S eff1 eff2 where  
      A:"\<Gamma> \<turnstile> (BI BooleanP) : U ; eff1"  "\<turnstile> U <: A1 \<rightarrow> T1 : Latent S" "\<Gamma> \<turnstile> v : T0 ; eff2" "\<turnstile> T0 <: A1"  "\<turnstile> T0 <: S"
      using prems by auto
    hence B:"U = Top \<rightarrow> BoolTy : Latent BoolTy " using bi_ty_elim[of \<Gamma> BooleanP U] by auto
    hence C:"\<turnstile> T0 <: BoolTy"      
      using prems arr_sub_arr_cases[of Top BoolTy "Latent BoolTy" _ _ "Latent S"] latent_eff.inject A by auto
    then obtain b where D:"v = Bool b" using A bool_value[of v \<Gamma> T0] prems by auto
    thus ?thesis using prems by auto
  qed

lemma booleanp_soundness_eff:
  assumes "\<Gamma> \<turnstile> App (BI BooleanP) v : T ; F" and "v : values" and "\<Delta> BooleanP v = Some u" and "\<Gamma> \<turnstile> u : T' ; F'"
  shows "\<turnstile> F' <e: F"
  proof -
    have cl:"closed u" using prems delta_closed[of BooleanP v u] by auto
    hence se:"simple_eff F'" using prems closed_eff by auto
    have or:"simple_eff F" using booleanp_eff_simple prems by auto
    thus ?thesis using prems
      proof (induct rule: simple_eff_cases)
        case NE thus ?case using se simple_eff_below_ne by auto
      next
        case FF thus ?case using false_ty_elim[of \<Gamma> T' F'] booleanp_FF_preserved by auto 
      next
        case TT thus ?case using true_ty_elim[of \<Gamma> T' F'] booleanp_TT_preserved by auto 
      qed
    qed

inductive_cases app_nump_ff: "\<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; FF"
thm app_nump_ff

lemma numberp_FF_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; FF" and "v : values" and "\<Delta> NumberP v = Some u"
  shows "u = Bool False"
  using `v : values` prems
  proof (induct v rule: values.induct)
    case (bool_value b) thus ?case by (cases b) auto
  next
    case (num_value b) 
    let ?P = "\<Gamma> \<turnstile> App (BI NumberP) (trm.Num b) : T1 ; FF" 
    have "?P ==> ?case"
      proof (ind_cases ?P)
        fix S T e1 e2 T0 eff1 eff2 U
        assume "App (BI NumberP) (trm.Num b) = App e1 e2"  "\<Gamma> \<turnstile> e1 : U ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
          "~ (\<turnstile> T <: S)" "e2 : values" "\<turnstile> U <:  T0 \<rightarrow> T1 : Latent S"
        hence a:"\<Gamma> \<turnstile> (BI NumberP) : U ; eff1 " using trm.inject by auto
        from prems have b:"\<Gamma> \<turnstile> Num b : T ; eff2" using trm.inject by auto
	have "U = Top \<rightarrow> BoolTy : Latent ty.Int" using a bi_ty_elim[of \<Gamma> NumberP "U"] by auto
	hence c:"S = ty.Int" using prems arr_sub_arr_cases[of Top _ _ T0 T1 "Latent S"] latent_eff.inject by auto
        from b have d:"T = ty.Int" using num_ty_elim by auto
        from c d have "\<turnstile> T <: S" by auto
        thus ?thesis using prems by auto
      qed
    thus ?case using num_value by auto
  qed (auto)

lemma numberp_TT_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; TT" and "v : values" and "\<Delta> NumberP v = Some u"
  shows "u = Bool True"
  proof -
    note app_ty_tt_elim[of \<Gamma> "(BI NumberP)" v T1]
    then obtain A1 U T0 T1 S eff1 eff2 where  
      A:"\<Gamma> \<turnstile> (BI NumberP) : U ; eff1"  "\<turnstile> U <: A1 \<rightarrow> T1 : Latent S" "\<Gamma> \<turnstile> v : T0 ; eff2" "\<turnstile> T0 <: A1"  "\<turnstile> T0 <: S"
      using prems by auto
    hence B:"U = Top \<rightarrow> BoolTy : Latent ty.Int " using bi_ty_elim[of \<Gamma> NumberP U] by auto
    hence C:"\<turnstile> T0 <: ty.Int"      
      using prems arr_sub_arr_cases[of Top BoolTy "Latent ty.Int" _ _ "Latent S"] latent_eff.inject A by auto
    then obtain b where D:"v = Num b" using A int_value[of v \<Gamma> T0] prems by auto
    thus ?thesis using prems by auto
  qed

lemma numberp_soundness_eff:
  assumes "\<Gamma> \<turnstile> App (BI NumberP) v : T ; F" and "v : values" and "\<Delta> NumberP v = Some u" and "\<Gamma> \<turnstile> u : T' ; F'"
  shows "\<turnstile> F' <e: F"
  proof -
    have cl:"closed u" using prems delta_closed[of NumberP v u] by auto
    hence se:"simple_eff F'" using prems closed_eff by auto
    have or:"simple_eff F" using numberp_eff_simple prems by auto
    thus ?thesis using prems
      proof (induct rule: simple_eff_cases)
        case NE thus ?case using se simple_eff_below_ne by auto
      next
        case FF thus ?case using false_ty_elim[of \<Gamma> T' F'] numberp_FF_preserved by auto 
      next
        case TT thus ?case using true_ty_elim[of \<Gamma> T' F'] numberp_TT_preserved by auto 
      qed
    qed

lemma empty_un_bot:
  fixes T :: ty
  shows "\<turnstile> Union [] <: T"
  by auto

lemma all_fun_ty_below:
  fixes S T :: ty
  shows "\<turnstile> S \<rightarrow> T : F <: (Union []) \<rightarrow> Top : latent_eff.NE"
  by (rule S_Fun) auto

inductive_cases below_latent_ne_cases: "\<turnstile> S \<rightarrow> T : F <: S' \<rightarrow> T' : latent_eff.NE"
thm below_latent_ne_cases

inductive_cases app_procp_ff: "\<Gamma> \<turnstile> (App (BI ProcP) v) :  T1 ; FF"
thm app_nump_ff
thm app_procp_ff

lemma procp_FF_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI ProcP) v) :  T1 ; FF" and "v : values" and "\<Delta> ProcP v = Some u"
  shows "u = Bool False"
  using `v : values` prems
  proof (nominal_induct v avoiding: \<Gamma> rule: values.strong_induct)
    case (bool_value b) thus ?case by (cases b) auto 
  next
    case (num_value b) thus ?case by auto 
  next
    case (abs_value x t b) 
    let ?P = "\<Gamma> \<turnstile> App (BI ProcP) (Lam[x:t].b) : T1 ; FF" 
    have "?P ==> ?case"
      proof (ind_cases ?P)
        fix e1 U eff1 T0 S e2 T eff2
        assume "App (BI ProcP) (Lam [x:t].b) = App e1 e2 ""  \<Gamma> \<turnstile> e1 : U ; eff1 "" \<turnstile> U <: T0 \<rightarrow> T1 : Latent S "
	  "\<Gamma> \<turnstile> e2 : T ; eff2 ""  \<turnstile> T <: T0 "" \<not> \<turnstile> T <: S "" e2 \<in> values "" closed e2"
        hence a:"\<Gamma> \<turnstile> (BI ProcP) : U ; eff1 " using trm.inject by auto
        from prems have b:"\<Gamma> \<turnstile> Lam[x:t].b : T ; eff2" using trm.inject by auto
	have "U = Top \<rightarrow> BoolTy : Latent (Union [] \<rightarrow> Top : latent_eff.NE)" using a bi_ty_elim[of \<Gamma> ProcP "U"] by auto
	hence c:"S = Union [] \<rightarrow> Top : latent_eff.NE" using prems arr_sub_arr_cases[of Top _ _ T0 T1 "Latent S"] latent_eff.inject by auto
        have "EX A1 A2 L. T = A1 \<rightarrow> A2 : L" using abs_ty_elim[OF b `x \<sharp> \<Gamma>`] by auto
	then obtain A1 A2 L where d:"T = A1 \<rightarrow> A2 : L" by auto
        from c d have "\<turnstile> T <: S" using all_fun_ty_below by auto
        thus ?thesis using prems by auto
      qed
    thus ?case using abs_value by auto
  next
    case (bi_value c)
    let ?P = "\<Gamma> \<turnstile> App (BI ProcP) (BI c) : T1 ; FF" 
    have "?P ==> ?case"
    proof (ind_cases ?P)
      fix e1 U eff1 T0 S e2 T eff2
      assume "App (BI ProcP) (BI c) = App e1 e2 ""  \<Gamma> \<turnstile> e1 : U ; eff1 "" \<turnstile> U <: T0 \<rightarrow> T1 : Latent S "
	"\<Gamma> \<turnstile> e2 : T ; eff2 ""  \<turnstile> T <: T0 "" \<not> \<turnstile> T <: S "" e2 \<in> values "" closed e2"
      hence a:"\<Gamma> \<turnstile> (BI ProcP) : U ; eff1 " using trm.inject by auto
      from prems have b:"\<Gamma> \<turnstile> (BI c) : T ; eff2" using trm.inject by auto
      have "U = Top \<rightarrow> BoolTy : Latent (Union [] \<rightarrow> Top : latent_eff.NE)" using a bi_ty_elim[of \<Gamma> ProcP "U"] by auto
      hence c:"S = Union [] \<rightarrow> Top : latent_eff.NE" using prems arr_sub_arr_cases[of Top _ _ T0 T1 "Latent S"] latent_eff.inject by auto
      have b':"T = \<Delta>\<^isub>\<tau> c" using bi_ty_elim[OF b] by auto
      hence "EX A1 A2 FA. T = A1 \<rightarrow> A2 : FA"  by (nominal_induct c rule: builtin.induct) auto
      then obtain A1 A2 F where d:"T = A1 \<rightarrow> A2 : F" by auto
      hence "\<turnstile> T <: S" using c d all_fun_ty_below by auto
      thus ?thesis using prems by auto
    qed
    thus ?case using bi_value by auto
  qed 

lemma proc_value:
  assumes "\<Gamma> \<turnstile> v : T ; F"
  and "v : values"
  and "\<turnstile> T <:  (A1 \<rightarrow> A2 : latent_eff.NE)"
  shows "EX x b t. v = Lam[x:t].b \<or> (EX c. v = BI c)"
  using `v : values` prems
proof (nominal_induct v avoiding: \<Gamma> rule: values.strong_induct)
  case abs_value thus ?case by auto
next
  case (bool_value b)
  hence "T = ty.TT \<or> T = ty.FF" using bool_ty_elim by auto
  thus ?case using sub_arr_cases[of T A1 A2 latent_eff.NE] using bool_value by auto
next
  case (num_value b)
  hence "T = ty.Int" using num_ty_elim by auto
  thus ?case using sub_arr_cases[of T A1 A2 latent_eff.NE] using num_value by auto
next
  case (bi_value c) thus ?case by auto
qed
      

lemma procp_TT_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI ProcP) v) :  T1 ; TT" and "v : values" and "\<Delta> ProcP v = Some u"
  shows "u = Bool True"
  proof -
    note app_ty_tt_elim[of \<Gamma> "(BI ProcP)" v T1]
    then obtain A1 U T0 T1 S eff1 eff2 where  
      A:"\<Gamma> \<turnstile> (BI ProcP) : U ; eff1"  "\<turnstile> U <: A1 \<rightarrow> T1 : Latent S" "\<Gamma> \<turnstile> v : T0 ; eff2" "\<turnstile> T0 <: A1"  "\<turnstile> T0 <: S"
      using prems by auto
    hence B:"U = Top \<rightarrow> BoolTy : Latent (Union [] \<rightarrow> Top : latent_eff.NE) " using bi_ty_elim[of \<Gamma> ProcP U] by auto
    hence C:"\<turnstile> T0 <:  (Union [] \<rightarrow> Top : latent_eff.NE)"      
      using prems arr_sub_arr_cases[of Top BoolTy "Latent  (Union [] \<rightarrow> Top : latent_eff.NE)" _ _ "Latent S"] latent_eff.inject A 
      by auto
    moreover
    {
      assume D:"EX x b t. v = Lam[x:t].b"
      then obtain x b t where "v = Lam[x:t].b" by auto
      hence ?thesis using prems by auto
    }
    moreover
    {
      assume "EX c. v = BI c"
      then obtain c where "v = BI c" by auto
      hence ?thesis using prems by (nominal_induct c rule: builtin.induct) auto
    }
    ultimately show ?thesis using prems proc_value[of \<Gamma> v T0 eff2 "Union []" Top] by auto
  qed

lemma procp_soundness_eff:
  assumes "\<Gamma> \<turnstile> App (BI ProcP) v : T ; F" and "v : values" and "\<Delta> ProcP v = Some u" and "\<Gamma> \<turnstile> u : T' ; F'"
  shows "\<turnstile> F' <e: F"
  proof -
    have cl:"closed u" using prems delta_closed[of ProcP v u] by auto
    hence se:"simple_eff F'" using prems closed_eff by auto
    have or:"simple_eff F" using procp_eff_simple prems by auto
    thus ?thesis using prems
      proof (induct rule: simple_eff_cases)
        case NE thus ?case using se simple_eff_below_ne by auto
      next
        case FF thus ?case using false_ty_elim[of \<Gamma> T' F'] procp_FF_preserved by auto 
      next
        case TT thus ?case using true_ty_elim[of \<Gamma> T' F'] procp_TT_preserved by auto 
      qed
    qed


text {* soundness of the \<Delta> rule *}

lemma bool_sub_boolty[simp]: "\<turnstile> ty.FF <: BoolTy" "\<turnstile> ty.TT <: BoolTy" by auto


lemma delta_soundness:
  assumes "\<Delta>\<^isub>\<tau> b = (T0 \<rightarrow> T1 : le)" and "v : values" and "\<Gamma> \<turnstile> v : T ; eff1" and "\<turnstile> T <: T0" 
  and "\<Gamma> \<turnstile> (App (BI b) v) : T1' ; eff" and "\<turnstile> T1 <: T1'"
  and "\<Delta> b v = Some u" and "valid \<Gamma>"
  shows "EX eff' T1'. \<Gamma> \<turnstile> u : T1' ; eff' \<and> \<turnstile> eff' <e: eff \<and> \<turnstile> T1' <: T1"
  using prems
proof (nominal_induct b rule: builtin.induct)
  case Add1
  hence a:"eff = NE" using add1_eff_ne[of \<Gamma> v T1' eff] by auto
  have "EX  eff'. \<Gamma> \<turnstile> u : T1 ; eff'" using `v : values` `valid \<Gamma>` Add1
    by (induct v rule: values.induct) (auto simp add: ty.inject)
  then obtain eff' where b:"\<Gamma> \<turnstile> u : T1 ; eff'" by auto
  have "simple_eff eff'" using delta_closed[of Add1 v u] closed_eff b Add1 by auto
  hence c:"\<turnstile> eff' <e: eff" using a simple_eff_below_ne by auto 
  from b c show ?case by auto
next
  case Nott
  hence a:"eff = NE" using nott_eff_ne[of \<Gamma> v T1' eff] by auto
  have "EX  eff' T1'. \<Gamma> \<turnstile> u : T1' ; eff' \<and> \<turnstile> T1' <: T1" using `v : values` `valid \<Gamma>` Nott
  proof (induct v rule: values.induct) 
    case (bool_value b)
    thus ?case using bool_value bool_sub_boolty by (cases b) auto
  next
    case num_value thus ?case using bool_sub_boolty by auto
  next
    case bi_value thus ?case using bool_sub_boolty by auto
  next
    case abs_value thus ?case using bool_sub_boolty by auto
  qed 
  then obtain eff' T1' where b:"\<Gamma> \<turnstile> u : T1' ; eff'" and b':"\<turnstile> T1' <: T1" by auto
  have "simple_eff eff'" using delta_closed[of Nott v u] closed_eff b Nott by auto
  hence c:"\<turnstile> eff' <e: eff" using a simple_eff_below_ne by auto 
  from b b' c show ?case by auto
next
  case BooleanP
  have "valid \<Gamma>" using typing_valid prems by auto
  have "T1 = BoolTy" using BooleanP by (simp add: ty.inject)
  then obtain bb where veq:"\<Delta> BooleanP v = Some (Bool bb)" by (nominal_induct v rule: trm.induct) (auto)
  hence "EX  T1' eff'. \<Gamma> \<turnstile> u : T1' ; eff' \<and> \<turnstile> T1' <: T1" 
    using `T1 = BoolTy` BooleanP bool_sub_boolty
  proof (cases bb)
    case True
    hence "u = Bool True" using veq BooleanP by auto
    hence "\<Gamma> \<turnstile> u : ty.TT; TT" using `valid \<Gamma>` by auto
    thus ?thesis using `T1 = BoolTy` bool_sub_boolty by auto
  next
    case False
    hence "u = Bool False" using veq BooleanP by auto
    hence "\<Gamma> \<turnstile> u : ty.FF; FF" using `valid \<Gamma>` by auto
    thus ?thesis using `T1 = BoolTy` bool_sub_boolty by auto
  qed
  then obtain T1a eff' where a:"\<Gamma> \<turnstile> u : T1a ; eff'" and a':"\<turnstile> T1a <: T1" by auto
  have c:"simple_eff eff'" using delta_closed[of BooleanP v u] closed_eff prems by auto  
  have b:"simple_eff eff" using BooleanP booleanp_eff_simple by auto
  hence "\<turnstile> eff' <e: eff" using b prems
  proof (induct rule: simple_eff_cases)
    case NE thus ?case using simple_eff_below_ne c by auto
  next
    case FF
    hence "u = Bool False" 
      using booleanp_FF_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI BooleanP) v : T1' ; eff` `\<Delta> BooleanP v = Some u` by auto
    hence "eff'= FF" using a false_ty_elim by auto
    thus ?case using FF by auto
  next
    case TT
    hence "u = Bool True" 
      using booleanp_TT_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI BooleanP) v : T1' ; eff` `\<Delta> BooleanP v = Some u` by auto
    hence "eff'= TT" using a true_ty_elim by auto
    thus ?case using TT by auto
  qed
  thus ?case using a a' by auto
next
  case NumberP
  have "valid \<Gamma>" using typing_valid prems by auto
  have "T1 = BoolTy" using NumberP by (simp add: ty.inject)
  then obtain bb where veq:"\<Delta> NumberP v = Some (Bool bb)" by (nominal_induct v rule: trm.induct) (auto)
  hence "EX  T1' eff'. \<Gamma> \<turnstile> u : T1' ; eff' \<and> \<turnstile> T1' <: T1" 
    using `T1 = BoolTy` NumberP bool_sub_boolty
  proof (cases bb)
    case True
    hence "u = Bool True" using veq NumberP by auto
    hence "\<Gamma> \<turnstile> u : ty.TT; TT" using `valid \<Gamma>` by auto
    thus ?thesis using `T1 = BoolTy` bool_sub_boolty by auto
  next
    case False
    hence "u = Bool False" using veq NumberP by auto
    hence "\<Gamma> \<turnstile> u : ty.FF; FF" using `valid \<Gamma>` by auto
    thus ?thesis using `T1 = BoolTy` bool_sub_boolty by auto
  qed
  then obtain T1a eff' where a:"\<Gamma> \<turnstile> u : T1a ; eff'" and a':"\<turnstile> T1a <: T1" by auto
  have c:"simple_eff eff'" using delta_closed[of NumberP v u] closed_eff prems by auto  
  have b:"simple_eff eff" using NumberP numberp_eff_simple by auto
  hence "\<turnstile> eff' <e: eff" using b prems
  proof (induct rule: simple_eff_cases)
    case NE thus ?case using simple_eff_below_ne c by auto
  next
    case FF
    hence "u = Bool False" 
      using numberp_FF_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI NumberP) v : T1' ; eff` `\<Delta> NumberP v = Some u` by auto
    hence "eff'= FF" using a false_ty_elim by auto
    thus ?case using FF by auto
  next
    case TT
    hence "u = Bool True" 
      using numberp_TT_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI NumberP) v : T1' ; eff` `\<Delta> NumberP v = Some u` by auto
    hence "eff'= TT" using a true_ty_elim by auto
    thus ?case using TT by auto
  qed
  thus ?case using a a' by auto
next
  case ProcP
  have "valid \<Gamma>" using typing_valid prems by auto
  have "T1 = BoolTy" using ProcP by (simp add: ty.inject)
  then obtain bb where veq:"\<Delta> ProcP v = Some (Bool bb)" by (nominal_induct v rule: trm.induct) (auto)
  hence "EX  T1' eff'. \<Gamma> \<turnstile> u : T1' ; eff' \<and> \<turnstile> T1' <: T1" 
    using `T1 = BoolTy` ProcP bool_sub_boolty
  proof (cases bb)
    case True
    hence "u = Bool True" using veq ProcP by auto
    hence "\<Gamma> \<turnstile> u : ty.TT; TT" using `valid \<Gamma>` by auto
    thus ?thesis using `T1 = BoolTy` bool_sub_boolty by auto
  next
    case False
    hence "u = Bool False" using veq ProcP by auto
    hence "\<Gamma> \<turnstile> u : ty.FF; FF" using `valid \<Gamma>` by auto
    thus ?thesis using `T1 = BoolTy` bool_sub_boolty by auto
  qed
  then obtain T1a eff' where a:"\<Gamma> \<turnstile> u : T1a ; eff'" and a':"\<turnstile> T1a <: T1" by auto
  have c:"simple_eff eff'" using delta_closed[of ProcP v u] closed_eff prems by auto  
  have b:"simple_eff eff" using ProcP procp_eff_simple by auto
  hence "\<turnstile> eff' <e: eff" using b prems
  proof (induct rule: simple_eff_cases)
    case NE thus ?case using simple_eff_below_ne c by auto
  next
    case FF
    hence "u = Bool False" 
      using procp_FF_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI ProcP) v : T1' ; eff` `\<Delta> ProcP v = Some u` by auto
    hence "eff'= FF" using a false_ty_elim by auto
    thus ?case using FF by auto
  next
    case TT
    hence "u = Bool True" 
      using procp_TT_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI ProcP) v : T1' ; eff` `\<Delta> ProcP v = Some u` by auto
    hence "eff'= TT" using a true_ty_elim by auto
    thus ?case using TT by auto
  qed
  thus ?case using a a' by auto
qed

lemma simple_eff_below_ve:
  assumes "simple_eff F"
  shows "\<turnstile> F <e: VE x"
  using prems
  by (induct F rule: simple_eff_cases) auto

lemma below_ne_simple:
  assumes "\<turnstile> F <e: G" and "G = NE"
  shows "simple_eff F"
  using prems no_sub_TT no_sub_FF
  by induct auto

lemma below_ve_simple:
  assumes "\<turnstile> F <e: G" and "G = VE x"
  shows "simple_eff F \<or> F = VE x"
  using prems
  by induct auto

consts
  remove_env  :: "'a list => 'a => 'a list" ("_ - _" [100,100] 100)

primrec
  "[] - x = []"
  "(y#xs) - x = (if x=y then (xs - x) else y#(xs - x))"

lemma fresh_remove:
  fixes a::"name"
  and   \<Gamma>::"(name\<times>ty) list"
  assumes a: "a\<sharp>\<Gamma>"
  shows "a\<sharp>(\<Gamma> - (x,T))"
using a
by (induct \<Gamma>) (auto simp add: fresh_list_cons)

lemma valid_remove:
  fixes pair::"name\<times>ty"
  assumes a: "valid \<Gamma>"
  shows "valid (\<Gamma> - (x,T))"
using a
by (induct \<Gamma>) (auto simp add: fresh_remove)

lemma set_remove:
  assumes a: "(a,T)\<in>set \<Gamma>"
  and     b: "a\<noteq>x"
  shows "(a,T)\<in>set (\<Gamma> - (x,T'))"
using a b
by (induct \<Gamma>) (auto)

lemma closed_elim:"closed e \<Longrightarrow> (supp e = ({}::name set))" using closed_def by auto

lemma set_remove_comm:
  shows "set (l - a) = (set l) - {a}"
  by (induct l) auto


lemma envplus_set:
  shows "set (\<Gamma> |+ TE T x) = (mapfun restrict T x) ` set \<Gamma>"
proof -
  have A:"!! a b. a = b \<Longrightarrow> set a = set b" by auto
  have "\<Gamma> |+ TE T x = map (mapfun restrict T x) \<Gamma>" by auto
  hence "set (\<Gamma> |+ TE T x) = set (map (mapfun restrict T x) \<Gamma>)" 
    using A[of "(\<Gamma> |+ TE T x)" "map (mapfun restrict T x) \<Gamma>"] by auto
  also have "\<dots> = (mapfun restrict T x) ` set \<Gamma>" by auto
  ultimately show ?thesis by auto
qed

lemma envminus_set:
  shows "set (\<Gamma> |- TE T x) = (mapfun remove T x) ` set \<Gamma>"
proof -
  have A:"!! a b. a = b \<Longrightarrow> set a = set b" by auto
  have "\<Gamma> |- TE T x = map (mapfun remove T x) \<Gamma>" by auto
  hence "set (\<Gamma> |- TE T x) = set (map (mapfun remove T x) \<Gamma>)" 
    using A[of "(\<Gamma> |- TE T x)" "map (mapfun remove T x) \<Gamma>"] by auto
  also have "\<dots> = (mapfun remove T x) ` set \<Gamma>" by auto
  ultimately show ?thesis by auto
qed



lemma envplus_set_ve:
  shows "set (\<Gamma> |+ VE x) = (mapfun remove ty.FF x) ` set \<Gamma>"
proof -
  have A:"!! a b. a = b \<Longrightarrow> set a = set b" by auto
  have "\<Gamma> |+ VE x = map (mapfun remove ty.FF x) \<Gamma>" by auto
  hence "set (\<Gamma> |+ VE x) = set (map (mapfun remove ty.FF x) \<Gamma>)" 
    using A[of "(\<Gamma> |+ VE x)" "map (mapfun remove ty.FF x) \<Gamma>"] by auto
  also have "\<dots> = (mapfun remove ty.FF x) ` set \<Gamma>" by auto
  ultimately show ?thesis by auto
qed

lemma envminus_set_ve:
  shows "set (\<Gamma> |- VE x) = (mapfun replace ty.FF x) ` set \<Gamma>"
proof -
  have A:"!! a b. a = b \<Longrightarrow> set a = set b" by auto
  have "\<Gamma> |- VE x = map (mapfun replace ty.FF x) \<Gamma>" by auto
  hence "set (\<Gamma> |- VE x) = set (map (mapfun replace ty.FF x) \<Gamma>)" 
    using A[of "(\<Gamma> |- VE x)" "map (mapfun replace ty.FF x) \<Gamma>"] by auto
  also have "\<dots> = (mapfun replace ty.FF x) ` set \<Gamma>" by auto
  ultimately show ?thesis by auto
qed


lemma fresh_weakening:
  assumes a:"x\<sharp>e" and b:"\<Gamma> \<turnstile> e : T ; F" and c: "valid \<Gamma>" 
  shows "(\<Gamma> - (x,T')) \<turnstile> e : T ; F"
  using b a c 
proof (nominal_induct \<Gamma> e T F avoiding: x T'  rule: typing.strong_induct)
  case T_Var thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case (T_App \<Gamma>' _ _ t1 t2) thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)
next
  case T_Abs thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_AbsPred thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_AppPred thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_IfTrue thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_IfFalse thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_True thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_False thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_Num thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_Const thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case (T_AppPredTrue \<Gamma>' e1 U F1 T0 T1 S e2 T F2 x T')
  have A:"x \<sharp> e1" "x \<sharp> e2" using T_AppPredTrue by auto
  hence "\<Gamma>' - (x,T') \<turnstile> e1 : U; F1" using T_AppPredTrue by auto
  also have "\<Gamma>' - (x,T') \<turnstile> e2 : T ; F2" using T_AppPredTrue A by auto
  ultimately show ?case using T_AppPredTrue(3) `\<turnstile> T <: T0` `\<turnstile> T <: S` by auto
next
  case (T_AppPredFalse  \<Gamma>' e1 U F1 T0 T1 S e2 T F2 x T')
  have A:"x \<sharp> e1" "x \<sharp> e2" using T_AppPredFalse by auto
  hence "\<Gamma>' - (x,T') \<turnstile> e1 : U ; F1" using T_AppPredFalse by auto
  also have "\<Gamma>' - (x,T') \<turnstile> e2 : T ; F2" using T_AppPredFalse A by auto
  ultimately show ?case using `~ (\<turnstile> T <: S)` `\<turnstile> T <: T0` `e2 : values` `closed e2`  T_AppPredFalse(3) by auto
next
  case (T_If \<Gamma>' e1 T1 F1 e2 T2 F2 e3 T3 F3 T x)
  have A:"x \<sharp> e1" "x \<sharp> e2" "x \<sharp> e3" using T_If by auto
  have "\<Gamma>' - (x,T') \<turnstile> e1 : T1 ; F1" using T_If A by auto
  thus ?case using T_If
    proof (nominal_induct "F1" rule: eff.induct)
      case NE
      from NE have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; eff.NE" by auto
      from NE have 2:"(\<Gamma>' - (x, T') |+ eff.NE) \<turnstile> e2 : T2 ; F2" by auto
      from NE have 3:"(\<Gamma>' - (x, T') |- eff.NE) \<turnstile> e3 : T3 ; F3" by auto
      from 1 2 3 show ?case using `\<turnstile> T2 <: T` `\<turnstile> T3 <: T` ..
    next
      case TT
      from TT have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; eff.TT" by auto
      from TT have 2:"(\<Gamma>' - (x, T') |+ eff.TT) \<turnstile> e2 : T2 ; F2" by auto
      from 1 2 show ?case using `\<turnstile> T2 <: T` by auto
    next
      case FF
      from FF have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; eff.FF" by auto
      from FF have 3:"(\<Gamma>' - (x, T') |+ eff.FF) \<turnstile> e3 : T3 ; F3" by auto
      from 1 3 show ?case using `\<turnstile> T3 <: T` by auto 
    next
      case (VE z)
      from VE have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; VE z" by auto
      have val1:"valid (\<Gamma>' |+ VE z)" using VE envplus_valid[of \<Gamma>' "VE z"] by auto
      have val2:"valid (\<Gamma>' |- VE z)" using VE envminus_valid[of \<Gamma>' "VE z"] by auto
      have "valid (\<Gamma>' |- VE z)" using VE envminus_valid[of \<Gamma>' "VE z"] by auto
      have A0:"!!T0 . (\<Gamma>' |- VE z) - (x, T0) \<turnstile> e3 : T3 ; F3" using VE(7) A `valid (\<Gamma>' |- VE z)` by auto

      have A:"!!T0 . (\<Gamma>' |+ VE z) - (x, T0) \<turnstile> e2 : T2 ; F2" using VE(5) A `valid (\<Gamma>' |+ VE z)` by auto
      let ?op = "replace"
      let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op ty.FF ty) else (v,ty)))"
      have B:"!! p. set ((\<Gamma>' |+ VE z) - p) = ((mapfun remove ty.FF z) ` (set \<Gamma>')) - {p}" 
	using envplus_set_ve set_remove_comm[of "(\<Gamma>' |+ VE z)"] by auto
      have image_lem:"!! f S v. (f ` S) - {(f v)} <= (f ` (S - {v}))" by auto
      note image_lem[of "mapfun remove ty.FF z" "set \<Gamma>'" "(x,T0)"]
      
      have eq1:"!! p. mapfun remove ty.FF z ` set \<Gamma>' - {mapfun remove ty.FF z p} = set ((\<Gamma>' |+ VE z) - (mapfun remove ty.FF z p))" using envplus_set_ve set_remove_comm[of "(\<Gamma>' |+ VE z)"] by auto

      have eq2:"!! p. mapfun remove ty.FF z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |+ VE z)"
      proof -
	fix p
	show "mapfun remove ty.FF z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |+ VE z)"
	  using envplus_set_ve[of _ "\<Gamma>' - p"]  set_remove_comm[of \<Gamma>'] by auto
      qed
      have eq3:"!! x T0. mapfun remove ty.FF z (x,T0) = (x, (if (x = z) then (remove ty.FF T0) else (T0)))" by auto
      let ?removeT' = "(if (x = z) then (remove ty.FF T') else (T'))"
      have goal:"((\<Gamma>' |+ VE z) - (x,?removeT')) \<lless> ((\<Gamma>' - (x,T')) |+ VE z)"
      proof -
	have " mapfun remove ty.FF z ` set \<Gamma>' - {mapfun remove ty.FF z (x,T')} <= 
	  mapfun remove ty.FF z ` (set \<Gamma>' - {(x,T')})" using  image_lem[of "mapfun remove ty.FF z" "set \<Gamma>'" "(x,T')"] by auto
	hence " mapfun remove ty.FF z ` set \<Gamma>' - {mapfun remove ty.FF z (x,T')} <= 
	  set ((\<Gamma>' - ((x,T'))) |+ VE z)" using eq2[of " (x, T')"] by auto
	hence "set ((\<Gamma>' |+ VE z) - (mapfun remove ty.FF z (x,T'))) <= 
	  set ((\<Gamma>' - ((x,T'))) |+ VE z)" 
	  using eq1[of "(x,T')"] by auto
	hence "set ((\<Gamma>' |+ VE z) - (x,?removeT')) <= set ((\<Gamma>' - (x,T')) |+ VE z)" using eq3 by auto
	thus ?thesis by auto
      qed
      have val3:"valid ((\<Gamma>' |+ VE z) - (x,?removeT'))" using val1 valid_remove by auto
      have "valid ((\<Gamma>' - (x, T')))" using `valid \<Gamma>'` valid_remove envplus_valid by auto
      hence val4:"valid ((\<Gamma>' - (x, T')) |+ VE z)" using  envplus_valid[of "\<Gamma>' - (x, T')" "VE z"] by auto
      from  A have "(\<Gamma>' |+ VE z) - (x,?removeT') \<turnstile>  e2 : T2 ; F2" by auto
      hence 2:"(\<Gamma>' - (x, T')) |+ VE z \<turnstile> e2 : T2 ; F2" using goal val3 val4
	weakening[of  "(\<Gamma>' |+ VE z) - (x,?removeT')" e2 T2 F2 "\<Gamma>' - (x,T') |+ VE z"] by auto

      have eq4:"!! p. mapfun replace ty.FF z ` set \<Gamma>' - {mapfun replace ty.FF z p} = set ((\<Gamma>' |- VE z) - (mapfun replace ty.FF z p))" using envminus_set_ve[of _ \<Gamma>'] set_remove_comm[of "(\<Gamma>' |- VE z)"] by auto

      have eq5:"!! p. mapfun replace ty.FF z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |- VE z)"
      proof -
	fix p
	show "mapfun replace ty.FF z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |- VE z)"
	  using envminus_set_ve[of _ "\<Gamma>' - p" ] set_remove_comm[of \<Gamma>'] by auto
      qed
      have eq6:"!! x T0. mapfun replace ty.FF z (x,T0) = (x, (if (x = z) then (replace ty.FF T0) else (T0)))" by auto
      let ?replaceT' = "(if (x = z) then (replace ty.FF T') else (T'))"
      have goal':"((\<Gamma>' |- VE z) - (x,?replaceT')) \<lless> ((\<Gamma>' - (x,T')) |- VE z)"
      proof -
	have " mapfun replace ty.FF z ` set \<Gamma>' - {mapfun replace ty.FF z (x,T')} <= 
	  mapfun replace ty.FF z ` (set \<Gamma>' - {(x,T')})" using  image_lem[of "mapfun replace ty.FF z" "set \<Gamma>'" "(x,T')"] by auto
	hence " mapfun replace ty.FF z ` set \<Gamma>' - {mapfun replace ty.FF z (x,T')} <= 
	  set ((\<Gamma>' - ((x,T'))) |- VE z)" using eq5[of " (x, T')"] by auto
	hence "set ((\<Gamma>' |- VE z) - (mapfun replace ty.FF z (x,T'))) <= 
	  set ((\<Gamma>' - ((x,T'))) |- VE z)" 
	  using eq4[of "(x,T')"] by auto
	hence "set ((\<Gamma>' |- VE z) - (x,?replaceT')) <= set ((\<Gamma>' - (x,T')) |- VE z)" using eq6 by auto
	thus ?thesis by auto
      qed
      have val5:"valid ((\<Gamma>' |- VE z) - (x,?replaceT'))" using val2 valid_remove by auto
      have "valid ((\<Gamma>' - (x, T')))" using `valid \<Gamma>'` valid_remove envminus_valid by auto
      hence val6:"valid ((\<Gamma>' - (x, T')) |- VE z)" using  envminus_valid[of "\<Gamma>' - (x, T')" "VE z"] by auto
      from  A0 have "(\<Gamma>' |- VE z) - (x,?replaceT') \<turnstile>  e3 : T3 ; F3" by auto
      hence 3:"(\<Gamma>' - (x, T')) |- VE z \<turnstile> e3 : T3 ; F3" using goal' val5 val6
	weakening[of  "(\<Gamma>' |- VE z) - (x,?replaceT')" e3 T3 F3 "\<Gamma>' - (x,T') |- VE z"] by auto
      from 1 2 3 show ?case using `\<turnstile> T2 <: T` `\<turnstile> T3 <: T` ..
    next
      case (TE U z)
      from TE have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; TE U z" by auto
      have val1:"valid (\<Gamma>' |+ TE U z)" using TE envplus_valid[of \<Gamma>' "TE U z"] by auto
      have val2:"valid (\<Gamma>' |- TE U z)" using TE envminus_valid[of \<Gamma>' "TE U z"] by auto
      have "valid (\<Gamma>' |- TE U z)" using TE envminus_valid[of \<Gamma>' "TE U z"] by auto
      have A0:"!!T0 . (\<Gamma>' |- TE U z) - (x, T0) \<turnstile> e3 : T3 ; F3" using TE(7) A `valid (\<Gamma>' |- TE U z)` by auto

      have A:"!!T0 . (\<Gamma>' |+ TE U z) - (x, T0) \<turnstile> e2 : T2 ; F2" using TE(5) A `valid (\<Gamma>' |+ TE U z)` by auto
      let ?op = "remove"
      let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op S ty) else (v,ty)))"
      have B:"!! p. set ((\<Gamma>' |+ TE U z) - p) = ((mapfun restrict U z) ` (set \<Gamma>')) - {p}" 
	using envplus_set set_remove_comm[of "(\<Gamma>' |+ TE U z)"] by auto
      have image_lem:"!! f S v. (f ` S) - {(f v)} <= (f ` (S - {v}))" by auto
      note image_lem[of "mapfun restrict U z" "set \<Gamma>'" "(x,T0)"]
      
      have eq1:"!! p. mapfun restrict U z ` set \<Gamma>' - {mapfun restrict U z p} = set ((\<Gamma>' |+ TE U z) - (mapfun restrict U z p))" using envplus_set set_remove_comm[of "(\<Gamma>' |+ TE U z)"] by auto

      have eq2:"!! p. mapfun restrict U z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |+ TE U z)"
      proof -
	fix p
	show "mapfun restrict U z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |+ TE U z)"
	  using envplus_set[of _ _ "\<Gamma>' - p"] set_remove_comm[of \<Gamma>'] by auto
      qed
      have eq3:"!! x T0. mapfun restrict U z (x,T0) = (x, (if (x = z) then (restrict U T0) else (T0)))" by auto
      let ?restrictT' = "(if (x = z) then (restrict U T') else (T'))"
      have goal:"((\<Gamma>' |+ TE U z) - (x,?restrictT')) \<lless> ((\<Gamma>' - (x,T')) |+ TE U z)"
      proof -
	have " mapfun restrict U z ` set \<Gamma>' - {mapfun restrict U z (x,T')} <= 
	  mapfun restrict U z ` (set \<Gamma>' - {(x,T')})" using  image_lem[of "mapfun restrict U z" "set \<Gamma>'" "(x,T')"] by auto
	hence " mapfun restrict U z ` set \<Gamma>' - {mapfun restrict U z (x,T')} <= 
	  set ((\<Gamma>' - ((x,T'))) |+ TE U z)" using eq2[of " (x, T')"] by auto
	hence "set ((\<Gamma>' |+ TE U z) - (mapfun restrict U z (x,T'))) <= 
	  set ((\<Gamma>' - ((x,T'))) |+ TE U z)" 
	  using eq1[of "(x,T')"] by auto
	hence "set ((\<Gamma>' |+ TE U z) - (x,?restrictT')) <= set ((\<Gamma>' - (x,T')) |+ TE U z)" using eq3 by auto
	thus ?thesis by auto
      qed
      have val3:"valid ((\<Gamma>' |+ TE U z) - (x,?restrictT'))" using val1 valid_remove by auto
      have "valid ((\<Gamma>' - (x, T')))" using `valid \<Gamma>'` valid_remove envplus_valid by auto
      hence val4:"valid ((\<Gamma>' - (x, T')) |+ TE U z)" using  envplus_valid[of "\<Gamma>' - (x, T')" "TE U z"] by auto
      from  A have "(\<Gamma>' |+ TE U z) - (x,?restrictT') \<turnstile>  e2 : T2 ; F2" by auto
      hence 2:"(\<Gamma>' - (x, T')) |+ TE U z \<turnstile> e2 : T2 ; F2" using goal val3 val4
	weakening[of  "(\<Gamma>' |+ TE U z) - (x,?restrictT')" e2 T2 F2 "\<Gamma>' - (x,T') |+ TE U z"] by auto

      have eq4:"!! p. mapfun remove U z ` set \<Gamma>' - {mapfun remove U z p} = set ((\<Gamma>' |- TE U z) - (mapfun remove U z p))" using envminus_set[of _ _ \<Gamma>'] set_remove_comm[of "(\<Gamma>' |- TE U z)"] by auto

      have eq5:"!! p. mapfun remove U z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |- TE U z)"
      proof -
	fix p
	show "mapfun remove U z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |- TE U z)"
	  using envminus_set[of _ _ "\<Gamma>' - p" ] set_remove_comm[of \<Gamma>'] by auto
      qed
      have eq6:"!! x T0. mapfun remove U z (x,T0) = (x, (if (x = z) then (remove U T0) else (T0)))" by auto
      let ?removeT' = "(if (x = z) then (remove U T') else (T'))"
      have goal':"((\<Gamma>' |- TE U z) - (x,?removeT')) \<lless> ((\<Gamma>' - (x,T')) |- TE U z)"
      proof -
	have " mapfun remove U z ` set \<Gamma>' - {mapfun remove U z (x,T')} <= 
	  mapfun remove U z ` (set \<Gamma>' - {(x,T')})" using  image_lem[of "mapfun remove U z" "set \<Gamma>'" "(x,T')"] by auto
	hence " mapfun remove U z ` set \<Gamma>' - {mapfun remove U z (x,T')} <= 
	  set ((\<Gamma>' - ((x,T'))) |- TE U z)" using eq5[of " (x, T')"] by auto
	hence "set ((\<Gamma>' |- TE U z) - (mapfun remove U z (x,T'))) <= 
	  set ((\<Gamma>' - ((x,T'))) |- TE U z)" 
	  using eq4[of "(x,T')"] by auto
	hence "set ((\<Gamma>' |- TE U z) - (x,?removeT')) <= set ((\<Gamma>' - (x,T')) |- TE U z)" using eq6 by auto
	thus ?thesis by auto
      qed
      have val5:"valid ((\<Gamma>' |- TE U z) - (x,?removeT'))" using val2 valid_remove by auto
      have "valid ((\<Gamma>' - (x, T')))" using `valid \<Gamma>'` valid_remove envminus_valid by auto
      hence val6:"valid ((\<Gamma>' - (x, T')) |- TE U z)" using  envminus_valid[of "\<Gamma>' - (x, T')" "TE U z"] by auto
      from  A0 have "(\<Gamma>' |- TE U z) - (x,?removeT') \<turnstile>  e3 : T3 ; F3" by auto
      hence 3:"(\<Gamma>' - (x, T')) |- TE U z \<turnstile> e3 : T3 ; F3" using goal' val5 val6
	weakening[of  "(\<Gamma>' |- TE U z) - (x,?removeT')" e3 T3 F3 "\<Gamma>' - (x,T') |- TE U z"] by auto
      from 1 2 3 show ?case using `\<turnstile> T2 <: T` `\<turnstile> T3 <: T` ..
    qed
  qed

lemma fresh_weakening_cons:
  assumes "valid ((a,S)#\<Gamma>)" (is "valid ?\<Gamma>") and "(a,S)# \<Gamma> \<turnstile> e : T ; F" and "a \<sharp> e"
  shows "\<Gamma> \<turnstile> e : T ; F"
  proof -
    have v1:"valid \<Gamma>" using prems valid_elim by blast
    hence v2:"valid (\<Gamma> - (a,S))" using valid_remove by auto
    have A:"?\<Gamma> - (a,S) \<turnstile> e : T ; F" using prems fresh_weakening[of a e ?\<Gamma> T F S] by auto
    have "?\<Gamma> - (a,S) = \<Gamma> - (a,S)" by auto
    hence B:"\<Gamma> - (a,S)  \<lless> \<Gamma>" by (induct \<Gamma>) auto
    thus ?thesis using A weakening[of _ e T F \<Gamma>] v1 v2 by auto
  qed
    

lemma closed_empty_env:
  assumes "closed e" and "\<Gamma> \<turnstile> e : T ; F" and "valid \<Gamma>"
  shows "[] \<turnstile> e : T ; F"
  using `valid \<Gamma>` prems
  proof (induct \<Gamma> rule: valid.induct)
    case v1 thus ?case by simp
  next
    case (v2 \<Gamma>' a S)
    have "a \<sharp> e" using `closed e` closed_def fresh_def[of a e] by auto
    thus ?case using v2 fresh_weakening_cons by auto
  qed



lemma closed_any_env:
  assumes "closed e" and "\<Gamma> \<turnstile> e : T ; F" and val1:"valid \<Gamma>" and val2:"valid \<Gamma>'"
  shows "\<Gamma>' \<turnstile> e : T ; F"
  using prems closed_empty_env weakening 
  proof -
    have A:"[] \<turnstile> e : T ; F" using prems closed_empty_env by auto
    note weakening
    have B:"[] \<lless> \<Gamma>'" by auto
    from A B val1 val2 have "\<Gamma>' \<turnstile> e : T ; F" using weakening by blast
    thus ?thesis by simp
  qed    

inductive_cases ve_ty_elim: "\<Gamma> \<turnstile> e : T ; VE x"  

lemma te_ty_elim: 
 "\<Gamma> \<turnstile> t1 : T ; TE U z \<Longrightarrow>
  EX f A A1 Fn S B. t1 = (App f (Var z)) \<and> \<Gamma> \<turnstile> f : B ; Fn \<and> \<turnstile> B <:  A1 \<rightarrow> T : Latent U \<and>
  \<Gamma> \<turnstile> (Var z) : A ; VE z \<and> \<turnstile> A <: A1 "
  proof (ind_cases "\<Gamma> \<turnstile> t1 : T ; TE U z")
    fix e1 T0 eff1 e2 Ta x S B
    assume "t1 = App e1 e2" "TE U z = TE S x"
      "\<Gamma> \<turnstile> e1 : B ; eff1 "" \<Gamma> \<turnstile> e2 : Ta ; VE x " "\<turnstile> B <: T0 \<rightarrow> T : Latent S"
      "\<turnstile> Ta <: T0"
    from prems have A:"e2 = Var x" using ve_ty_elim[of \<Gamma> e2 Ta x]  eff.inject by auto
    hence B:"t1 = App e1 (Var z)" using prems trm.inject eff.inject by auto
    have C:" \<Gamma> \<turnstile> (Var z) : Ta ; VE z" using prems A trm.inject eff.inject by auto
    have D:" \<Gamma> \<turnstile> e1 : B ; eff1" using ty.inject latent_eff.inject prems eff.inject by auto
    have E:"\<turnstile> B <: T0 \<rightarrow> T : Latent U" using ty.inject latent_eff.inject prems eff.inject by auto
    from `\<turnstile> Ta <: T0` B C D E  show ?thesis by blast
  qed
    
  

lemma unique_var_typing:
  assumes  "(x,T)#\<Gamma> \<turnstile> Var x : T; VE x" and "(x,T)#\<Gamma> \<turnstile> Var x : T' ; VE x"
  shows "T = T'"
  proof (rule ccontr)
    assume "T ~= T'"
    have "(x,T) : set ((x,T)#\<Gamma>)" using var_ty_elim[of _ x T "VE x"] prems by auto
    have "(x,T') : set ((x,T)#\<Gamma>)" "valid ((x,T)#\<Gamma>)" using var_ty_elim[of "((x,T)#\<Gamma>)" x T' "VE x"] prems by auto
    hence A:"(x,T') : set \<Gamma>" "valid \<Gamma>" "x \<sharp> \<Gamma>" using prems valid_elim[of x T \<Gamma>] by auto
    have "x : supp \<Gamma>" using `valid \<Gamma>` A
    proof (induct \<Gamma> rule: valid.induct)
      case v1 thus ?case by auto
    next
      case (v2 \<Gamma>' a S) 
      hence "x \<sharp> (a,S)" "x \<sharp> \<Gamma>'" using fresh_list_cons by auto
      hence "x \<sharp> a" by auto
      hence "x ~= a" using fresh_atm by auto
      hence "(x,T') : set \<Gamma>'" using v2 by auto
      have "valid \<Gamma>'" using v2 valid_elim[of a S \<Gamma>'] by auto
      hence "x : supp \<Gamma>'" using v2 `(x,T') : set \<Gamma>'` `x \<sharp> \<Gamma>'` by auto
      hence "x : supp (a,S)  \<union> supp \<Gamma>'" by auto
      hence "x : (supp ((a,S)#\<Gamma>') :: name set)" using supp_list_cons[of "(a,S)" \<Gamma>'] by force
      thus ?case by simp 
    qed
    hence "~ (x \<sharp> \<Gamma>)" using fresh_def[of x \<Gamma>] by blast
    thus False using `x \<sharp> \<Gamma>` by auto
  qed

inductive_cases tt_sub_ff:"\<turnstile> ty.TT <: ty.FF"
inductive_cases ff_sub_tt:"\<turnstile> ty.FF <: ty.TT"

lemma value_effect_tt_or_ff:
  assumes "v : values" and "\<Gamma> \<turnstile> v : T ; F"
  shows "F = FF \<and> v = Bool False \<or> F = TT \<and> v ~= Bool False"
  using prems
proof (nominal_induct v avoiding: \<Gamma> rule: values.strong_induct)
  case num_value thus ?case using num_ty_elim by auto
next
  case bi_value thus ?case using bi_ty_elim by auto
next
  case abs_value thus ?case using abs_ty_elim[of \<Gamma> _ _ _ T F] by auto
next
  case (bool_value b)
  thus ?case using true_ty_elim false_ty_elim by (cases b) auto
qed

lemma remove_fresh_env:
  assumes A:"y \<sharp> \<Gamma>" and B:"valid \<Gamma>"
  shows "\<Gamma> - (y,T) = \<Gamma>"
  using B A
proof (induct \<Gamma> rule: valid.induct)
  case v1 thus ?case by auto
next
  case (v2 \<Gamma>' a S)
  have "y \<noteq> a" "y \<sharp> \<Gamma>'" using `y \<sharp> ((a, S) # \<Gamma>')` using fresh_atm[of y a] fresh_list_cons by auto
  hence "((a, S) # \<Gamma>') - (y, T) = (a, S) # (\<Gamma>' - (y, T))" by auto
  thus ?case using v2 `y \<sharp> \<Gamma>'` by auto
qed


lemma subst_preserve_TE_app:
  assumes tapp:"(y,T0)#\<Gamma> \<turnstile> App e1 e2 : T ; TE S x"
  and neq:"y \<noteq> x"
  and val:"valid ((y,T0)#\<Gamma>)"
  and ih: "!! t bc bf . \<lbrakk>t \<guillemotleft> App e1 e2;  (y, T0) # \<Gamma> \<turnstile> t : bc ; bf \<rbrakk> 
  \<Longrightarrow> \<exists>T' F'.  \<Gamma> \<turnstile> t[y::=v] : T' ; F'  \<and> \<turnstile> T' <: bc \<and> \<turnstile> F' <e: bf"
  shows "\<Gamma> \<turnstile> (App e1 e2)[y::=v] : T ; TE S x"
proof -
  note te_ty_elim[OF tapp]
  then obtain f  A A1 Fn Sa B
    where sz:"App e1 e2 = App f (Var x)"
    and tf:"(y, T0) # \<Gamma> \<turnstile> f : B ; Fn  "" \<turnstile> B <: A1 \<rightarrow> T : Latent S" 
    and tvx:"(y, T0) # \<Gamma> \<turnstile> Var x : A ; VE x" and sub:" \<turnstile> A <: A1"
    by auto
  hence "e1 = f" and "e2 = Var x" using trm.inject by auto
  hence "e2[y::=v] = Var x" using `y \<noteq> x` forget by auto
  hence tsub:" (y, T0)#\<Gamma> \<turnstile> e2[y::=v] : A ; VE x" using `e2=Var x` tvx by auto
  have fr:"y \<sharp> e2[y::=v]" using `e2 = Var x``e2[y::=v] = Var x` `y \<noteq> x` using fresh_atm by auto
  have "y \<sharp> \<Gamma>" "valid \<Gamma>" using valid_elim[OF val] by auto
  hence "((y, T0) # \<Gamma>) - (y, T0) = \<Gamma>" using remove_fresh_env[OF `y \<sharp> \<Gamma>` `valid \<Gamma>`] by auto
  hence te2:"\<Gamma> \<turnstile> e2[y::=v] : A ; VE x" using fresh_weakening[OF fr tsub `valid ((y,T0)#\<Gamma>)`, of T0]  by auto
  have szf:"f \<guillemotleft> App e1 e2" using sz by auto
  note ih[OF szf tf(1)]
  then obtain T' F' where  tfsub:"\<Gamma> \<turnstile> f[y::=v] : T' ; F'  "" \<turnstile> T' <: B " "\<turnstile> F' <e: Fn" by auto
  hence " \<turnstile> T' <: A1 \<rightarrow> T : Latent S " using  `\<turnstile> B <: A1 \<rightarrow> T : Latent S` by auto
  hence "\<Gamma> \<turnstile> (App f e2)[y::=v] : T ; TE S x" using te2 tfsub `\<turnstile> A <: A1` by auto
  thus ?thesis using sz using trm.inject by auto
qed

inductive_cases te_elim_auto: "\<Gamma> \<turnstile> e : T ; TE S x"
thm te_elim_auto

lemma subst_preserve_TE:
  fixes v
  assumes tapp:"(y,T0)#\<Gamma> \<turnstile> e : T ; TE S x"
  and neq:"y \<noteq> x"
  and val:"valid ((y,T0)#\<Gamma>)"
  and ih: "!! t bc bf . \<lbrakk>t \<guillemotleft> e;  (y, T0) # \<Gamma> \<turnstile> t : bc ; bf \<rbrakk> 
  \<Longrightarrow> \<exists>T' F'.  \<Gamma> \<turnstile> t[y::=v] : T' ; F'  \<and> \<turnstile> T' <: bc \<and> \<turnstile> F' <e: bf"
  shows "\<Gamma> \<turnstile> e[y::=v] : T ; TE S x"
proof -
  obtain e1 e2 where "e = App e1 e2" using te_elim_auto[OF tapp, of thesis] by auto
  hence A:"(y,T0)#\<Gamma> \<turnstile> App e1 e2 : T ; TE S x" using tapp by auto
  note subst_preserve_TE_app[OF A neq val , of v]
  have "!! t bc bf . \<lbrakk>t \<guillemotleft> App e1 e2;  (y, T0) # \<Gamma> \<turnstile> t : bc ; bf \<rbrakk> 
    \<Longrightarrow> \<exists>T' F'.  \<Gamma> \<turnstile> t[y::=v] : T' ; F'  \<and> \<turnstile> T' <: bc \<and> \<turnstile> F' <e: bf" using ih `e = App e1 e2` by auto
  hence "\<Gamma> \<turnstile> App e1 e2[y::=v] : T ; TE S x" using subst_preserve_TE_app[OF A neq val , of v] by auto
  thus ?thesis using `e = App e1 e2` by auto
qed
  
inductive_cases lam_latent_eff_elim_auto: "\<Gamma> \<turnstile> Lam[x:T].b : S1 \<rightarrow> S2 : Latent U ; F"
thm lam_latent_eff_elim_auto

lemma preserve_subst:
  assumes "(x,T0)#\<Gamma> \<turnstile> e : T ; F" and "\<Gamma> \<turnstile> e' : T1 ; G" and "\<turnstile> T1 <: T0" and "valid ((x,T0)#\<Gamma>)" 
  and "closed e'" and "e' : values"
  shows "EX T' F'. \<Gamma> \<turnstile> e[x::=e'] : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F"
  using prems
proof (nominal_induct e avoiding: \<Gamma> x e' T T1 T0 F G rule: trm_comp_induct)
  case (Var v)
  have a1: "\<Gamma> \<turnstile>e':T1;G" by fact
  have a2: "((x,T0)#\<Gamma>) \<turnstile> Var v:T;F" by fact
  hence a21: "(v,T)\<in>set((x,T0)#\<Gamma>)" and a22: "valid((x,T0)#\<Gamma>)" and a22b:"F = VE v"
    using var_ty_elim[of "(x, T0) # \<Gamma>"] by auto
  from a22 have a23: "valid \<Gamma>" and a24: "x\<sharp>\<Gamma>" by (auto dest: valid_elim) 
  from a24 have a25: "\<not>(\<exists>\<tau>. (x,\<tau>)\<in>set \<Gamma>)" by (rule fresh_context)
  show ?case
  proof (cases "v=x")
    assume case1: "v=x"
    hence "(Var v)[x::=e'] = e'" by simp
    hence A:"\<Gamma> \<turnstile> (Var v)[x::=e'] : T1; G" using Var by auto
    have "simple_eff G" using closed_eff `closed e'` prems by auto
    hence C:"\<turnstile> G <e: F" using a22b simple_eff_below_ve by auto
    have B:"T = T0"
    proof (rule ccontr)
      assume a3:"T ~= T0"
      from a3 a21 have "(v,T)\<in>set \<Gamma>" by force
      with case1 a25 show False by force 
    qed
    hence D:"\<turnstile> T1 <: T" using  `\<turnstile> T1 <: T0` by auto
    have "~ (\<exists>S y. F = TE S y)" using a22b by auto
    thus ?thesis using A a22b C D by blast
  next
    assume case2: "v\<noteq>x"
    with a21 have a26: "(v,T)\<in>set \<Gamma>" by force
    have a27:" Var v[x::=e'] = Var v" using case2 by simp
    from a23 a26 a27 have "\<Gamma> \<turnstile> Var v:T;VE v" by force
    thus ?thesis using a27 a22b by auto
  qed
next
  case (Num n)
  have A:"(Num n)[x::=e'] = Num n" by auto
  have B:"F = eff.TT" using Num num_ty_elim by auto
  have "T = ty.Int" using num_ty_elim Num by auto
  hence "\<Gamma> \<turnstile> (Num n)[x::=e'] : T ; eff.TT" using Num A valid_elim[of x T0 \<Gamma>] by auto
  thus ?case using Num B by auto
next
  case (Bool b)
  have v:"valid \<Gamma>" using prems typing_valid by auto
  have A:"(Bool b)[x::=e'] = Bool b" by auto
  thus ?case 
  proof (cases b)
    case True
    hence B:"T = ty.TT" and "F = TT" using Bool true_ty_elim by auto
    thus ?thesis using A v True by auto
  next
    case False
    hence B:"T = ty.FF" and "F = FF" using Bool false_ty_elim by auto
    thus ?thesis using A v False by auto
  qed
next
  case (BI b)
  have A:"(BI b)[x::=e'] = (BI b)" by auto
  have B:"F = eff.TT" using BI bi_ty_elim by auto
  have "T = \<Delta>\<^isub>\<tau> b" using bi_ty_elim BI by auto
  hence "\<Gamma> \<turnstile> (BI b)[x::=e'] : T ; eff.TT" using BI A valid_elim[of x T0 \<Gamma>] by  auto
  thus ?case using BI B by auto
next
  case (App s1 s2 \<Gamma>' x' e'' T' T1' T0' F' G')
  have ih_s1: "\<And>c \<sigma> T F T' F' e' \<Gamma>. ((c,\<sigma>)#\<Gamma>) \<turnstile> s1:T; F \<Longrightarrow> closed e' \<Longrightarrow> e' : values \<Longrightarrow> valid ((c,\<sigma>)#\<Gamma>) \<Longrightarrow> \<Gamma>\<turnstile> e': T' ; F' \<Longrightarrow> \<turnstile> T' <: \<sigma> \<Longrightarrow> EX S G. \<Gamma> \<turnstile> s1[c::=e']:S ; G \<and> \<turnstile> S <: T \<and> \<turnstile> G <e: F" .
  have ih_s2: "\<And>c \<sigma> T F T' F' e' \<Gamma>. ((c,\<sigma>)#\<Gamma>) \<turnstile> s2:T; F \<Longrightarrow> closed e' \<Longrightarrow> e' : values \<Longrightarrow> valid ((c,\<sigma>)#\<Gamma>) \<Longrightarrow> \<Gamma>\<turnstile> e': T' ; F' \<Longrightarrow> \<turnstile> T' <: \<sigma> \<Longrightarrow> EX S G. \<Gamma> \<turnstile> s2[c::=e']:S ; G \<and> \<turnstile> S <: T \<and> \<turnstile> G <e: F" .
  have appty:"((x',T0')#\<Gamma>')\<turnstile>App s1 s2 : T'; F'" .
  from appty have
    elim1:"\<exists>T0 T0'a T1 le eff' eff'' U.(x',T0')#\<Gamma>' \<turnstile> s1 :U;eff' \<and> (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff'' \<and> \<turnstile> U <: T0\<rightarrow>T1:le \<and> \<turnstile> T0'a <: T0 \<and> T1 = T'"
    using app_ty_elim by auto
  from appty 
  have elim2:"(x', T0') # \<Gamma>' \<turnstile> App s1 s2 : T' ; FF \<Longrightarrow> \<exists>T0 T0'a leS eff' eff'' le U.(x',T0')#\<Gamma>' \<turnstile> s1 :U;eff' \<and> 
    (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff''  \<and> \<turnstile> T0'a <: T0\<and> \<turnstile> U <: T0\<rightarrow>T':le \<and> le = Latent leS  \<and> ~ (\<turnstile> T0'a <: leS) \<and> s2 : values \<and> closed s2"
    using app_ty_ff_elim[of "((x',T0')#\<Gamma>')" s1 s2 T'] by blast
  have elim3:"(x', T0') # \<Gamma>' \<turnstile> App s1 s2 : T' ; TT \<Longrightarrow> \<exists>T0 T0'a leS eff' eff'' U le.(x',T0')#\<Gamma>' \<turnstile> s1 :U;eff' \<and> 
    (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff'' \<and> \<turnstile> T0'a <: T0  \<and> \<turnstile> U <: T0\<rightarrow>T':le \<and> le = Latent leS \<and> \<turnstile> T0'a <: leS " 
    using app_ty_tt_elim[of "((x',T0')#\<Gamma>')" s1 s2 T'] by blast
  from elim1  obtain T0 T0'a T1 le eff' eff'' U where
    P:"(x',T0')#\<Gamma>' \<turnstile> s1 :U;eff'"" (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff''"" \<turnstile> T0'a <: T0 "" T1 = T'" "\<turnstile> U <: T0\<rightarrow>T1:le" by auto
  hence "EX S1 G1. \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 \<and> \<turnstile> S1 <: U \<and> \<turnstile> G1 <e: eff'"
    using ih_s1 App by auto
  then obtain S1 G1 where Q:" \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 "" \<turnstile> S1 <: U" "\<turnstile> G1 <e: eff'" by auto
  have sub1:"\<turnstile>S1 <: T0\<rightarrow>T1:le" using P Q by auto
    (* then apply ih_s2, get something about the substition of s2, and put it all back together. *)
  from P have "EX S G. \<Gamma>' \<turnstile> s2[x'::=e'']:S ; G \<and> \<turnstile> S <: T0'a \<and> \<turnstile> G <e: eff''"
    using ih_s2[of x' T0' \<Gamma>' T0'a eff''] App by auto
  then obtain S2 G2 where S:"\<Gamma>' \<turnstile> s2[x'::=e'']:S2 ; G2 "" \<turnstile> S2 <: T0'a" "\<turnstile> G2 <e: eff''" by auto
  let ?ns1 = "s1[x'::=e'']" and ?ns2 = "s2[x'::=e'']"
  have sub2:"\<turnstile> S2 <: T0" using P S by auto
  have L1:"\<Gamma>' \<turnstile> App ?ns1 ?ns2 : T1 ; NE" using Q S sub1 sub2 by auto
  have L2:"T1 = T'" .
  show ?case using appty
  proof (nominal_induct F' rule: eff.induct)
    case NE thus ?case using L1 L2 by auto
  next
    case VE thus ?case using L1 L2 by auto
  next
    case (TE ty var) thus ?case using L1 L2 by auto
  next
    case TT
    from elim3 TT  obtain T0 T0'a T1 le leS eff' eff'' U where
      P:"(x',T0')#\<Gamma>' \<turnstile> s1 :U;eff'"" (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff''"" \<turnstile> T0'a <: T0 "" T1 = T'" "\<turnstile> U <: T0\<rightarrow>T1:le"
      "le = Latent leS" "\<turnstile> T0'a <: leS" by auto
    hence "EX S1 G1. \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 \<and> \<turnstile> S1 <: U \<and> \<turnstile> G1 <e: eff'"
      using ih_s1 App by blast
    then obtain S1 G1 where Q:" \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 "" \<turnstile> S1 <: U" "\<turnstile> G1 <e: eff'" by auto
    hence R:"\<turnstile> S1 <: T0\<rightarrow>T1:le" using P by auto
      (* then apply ih_s2, get something about the substition of s2, and put it all back together. *)
    from P have "EX S G. \<Gamma>' \<turnstile> s2[x'::=e'']:S ; G \<and> \<turnstile> S <: T0'a \<and> \<turnstile> G <e: eff''"
      using ih_s2[of x' T0' \<Gamma>' T0'a eff''] App by auto
    then obtain S2 G2 where S:"\<Gamma>' \<turnstile> s2[x'::=e'']:S2 ; G2 "" \<turnstile> S2 <: T0'a" "\<turnstile> G2 <e: eff''" by auto
    let ?ns1 = "s1[x'::=e'']" and ?ns2 = "s2[x'::=e'']"
    have noover: "\<turnstile> S2 <: leS" using `\<turnstile> S2 <: T0'a` `\<turnstile> T0'a <: leS` by auto
    have L1:"\<Gamma>' \<turnstile> App ?ns1 ?ns2 : T1 ; TT" using P Q R S noover T_AppPredFalse[of \<Gamma>' " s1[x'::=e'']" U] by auto
    have L2:"T1 = T'" .
    from L1 L2 show ?case by auto
  next
    case FF
    from elim2 FF  obtain T0 T0'a T1 le leS eff' eff'' U where
      P:"(x',T0')#\<Gamma>' \<turnstile> s1 :U;eff'"" (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff''"" \<turnstile> T0'a <: T0 "" T1 = T'" "\<turnstile> U <: T0\<rightarrow>T1:le"
      "le = Latent leS" "~ (\<turnstile> T0'a <: leS)" "s2 :values" "closed s2" by auto
    hence "EX S1 G1. \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 \<and> \<turnstile> S1 <: U \<and> \<turnstile> G1 <e: eff'"
      using ih_s1 App by auto
    then obtain S1 G1 where Q:" \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 "" \<turnstile> S1 <: U" "\<turnstile> G1 <e: eff'" by auto
    hence R:"\<turnstile> S1 <: T0\<rightarrow>T1:le" using P by auto
      (* then apply ih_s2, get something about the substition of s2, and put it all back together. *)
    from P have "EX S G. \<Gamma>' \<turnstile> s2[x'::=e'']:S ; G \<and> \<turnstile> S <: T0'a \<and> \<turnstile> G <e: eff''"
      using ih_s2[of x' T0' \<Gamma>' T0'a eff''] App by auto
    then obtain S2 G2 where S:"\<Gamma>' \<turnstile> s2[x'::=e'']:S2 ; G2 "" \<turnstile> S2 <: T0'a" "\<turnstile> G2 <e: eff''" by auto
    let ?ns1 = "s1[x'::=e'']" and ?ns2 = "s2[x'::=e'']"
    have "x' \<sharp> s2" using closed_def fresh_def[of x' s2] `closed s2` by auto
    hence "s2 = ?ns2" using forget by auto
    hence S':"\<Gamma>' \<turnstile> ?ns2 : T0'a ; eff''" 
      using `(x',T0')#\<Gamma>' \<turnstile> s2 : T0'a ; eff''` fresh_weakening_cons `valid ((x',T0')#\<Gamma>')` `x' \<sharp> s2`
      by auto

    have noover: "~(\<turnstile> T0'a <: leS)" .
    have T:"closed ?ns2" "?ns2 : values" using `s2 = ?ns2` `closed s2` `s2 : values` by auto
    have L1:"\<Gamma>' \<turnstile> App ?ns1 ?ns2 : T1 ; FF" using P Q R S' T noover  by auto
    have L2:"T1 = T'" by fact
    from L1 L2 show ?case by auto
  qed
next
  case (Lam a body \<Gamma>' x' e''  T' T1' T0' F' G' ty )
  hence f1: "a\<sharp>\<Gamma>'" and f2: "a\<noteq>x'" and f2': "x'\<sharp>a" and f3: "a\<sharp>e''" and f4: "a\<sharp>((x',T0')#\<Gamma>')"
    by (auto simp add: fresh_atm fresh_prod fresh_list_cons)
  have c1: "((x',T0')#\<Gamma>')\<turnstile>Lam [a:ty].body : T' ; F'" by fact
(*  hence "\<exists>\<tau>2 eff L S. ((a,ty)#(x',T0')#\<Gamma>') \<turnstile> body : \<tau>2 ; eff \<and> T'=ty\<rightarrow>\<tau>2:L  \<and> F' = TT" using f4 abs_ty_elim by auto *)
  then obtain \<tau>2 eff L S where c11: "T'=ty\<rightarrow>\<tau>2:L" and c12: "((a,ty)#(x',T0')#\<Gamma>') \<turnstile> body : \<tau>2 ; eff" and "F' = TT"
    and c13:"L = latent_eff.NE \<or> (eff = TE S a \<and> L = Latent S)" using f4 abs_ty_elim by blast
  from c12 have "valid ((a,ty)#(x',T0')#\<Gamma>')" using Lam by auto
  hence ca: "valid \<Gamma>'" and cb: "a\<sharp>\<Gamma>'" and cc: "x'\<sharp>\<Gamma>'" 
    by (auto dest: valid_elim simp add: fresh_list_cons)
  have c2: "((a,ty)#(x',T0')#\<Gamma>') \<lless> ((x',T0')#(a,ty)#\<Gamma>')" by force
  have c3: "valid ((x',T0')#(a,ty)#\<Gamma>')"
    by (rule v2, rule v2, auto simp add: fresh_list_cons fresh_prod ca cb cc f2' fresh_ty)
  from c12 c2 c3 have c14: "((x',T0')#(a,ty)#\<Gamma>') \<turnstile> body : \<tau>2 ; eff" using `valid ((a, ty) # (x', T0') # \<Gamma>')`
    by (force intro: weakening)
  let ?inner\<Gamma> = "(a,ty)#\<Gamma>'"
  have validig:"valid ?inner\<Gamma>" using `a \<sharp> \<Gamma>'` `valid \<Gamma>'` by auto
  have c15:"\<Gamma>' \<lless>  ?inner\<Gamma>" by auto
  hence c16:"?inner\<Gamma> \<turnstile> e'' : T1' ; G'"
    using weakening[of \<Gamma>' _ _ _ ?inner\<Gamma>] `\<Gamma>' \<turnstile> e'' : T1' ; G'` validig `valid \<Gamma>'` by simp
  have "EX TA0 FA0. ?inner\<Gamma> \<turnstile> body[x'::=e''] : TA0 ; FA0 \<and> \<turnstile> TA0 <: \<tau>2 \<and> \<turnstile> FA0 <e: eff"
    using c16 Lam(10)[of x' T0' ?inner\<Gamma> \<tau>2 eff e'' T1' G'] ` \<turnstile> T1' <: T0'` `valid ((x', T0') # (a, ty) # \<Gamma>')` c14 `closed e''`
    `e'' : values`
    by auto
  then obtain TA0 FA0 where body_ty:"?inner\<Gamma> \<turnstile> body[x'::=e''] : TA0 ; FA0 "" \<turnstile> TA0 <: \<tau>2" by auto
  hence L11:"\<Gamma>' \<turnstile> (Lam[a:ty].(body[x'::=e''])) : ty \<rightarrow> TA0 : latent_eff.NE; eff.TT" using `a \<sharp> \<Gamma>'` by auto 
  note Lam(9)[OF _ _ `(a, ty)# \<Gamma>' \<turnstile> e'' : T1' ; G'` `\<turnstile> T1' <: T0'` `valid ((x', T0')# (a, ty) # \<Gamma>')` `closed e''` `e'' : values`]
  hence "!! t bc bf . \<lbrakk>t \<guillemotleft> Lam [a:ty].body;  (x', T0') #(a, ty)# \<Gamma>' \<turnstile> t : bc ; bf \<rbrakk>
\<Longrightarrow> \<exists>T' F'.  (a, ty)#\<Gamma>' \<turnstile> t[x'::=e''] : T' ; F'  \<and> \<turnstile> T' <: bc \<and> \<turnstile> F' <e: bf" .
  hence ih_body:"!! t bc bf . \<lbrakk>t \<guillemotleft> body;  (x', T0') # (a, ty)#\<Gamma>' \<turnstile> t : bc ; bf \<rbrakk>
\<Longrightarrow> \<exists>T' F'.  (a, ty)#\<Gamma>' \<turnstile> t[x'::=e''] : T' ; F'  \<and> \<turnstile> T' <: bc \<and> \<turnstile> F' <e: bf" by auto
  hence L12:"L = Latent S \<Longrightarrow> \<Gamma>' \<turnstile> (Lam[a:ty].(body[x'::=e''])) : ty \<rightarrow> \<tau>2 : Latent S; eff.TT" 
  proof -
    assume "L = Latent S"
    hence "eff = TE S a" using c13 by auto
    hence c12':"(a, ty) # (x', T0') # \<Gamma>' \<turnstile> body : \<tau>2 ; TE S a" using c12 by simp
    have c12'':" (x', T0') # (a, ty) # \<Gamma>' \<turnstile> body : \<tau>2 ; TE S a" using weakening[OF c12' _ c2 ] 
      using `valid ((x', T0') # (a, ty) # \<Gamma>')` `valid ((a, ty) # (x', T0') # \<Gamma>')` by auto
    have f2':"x' \<noteq> a" using f2 by auto
    note body_ty subst_preserve_TE[OF c12'' f2' `valid ((x', T0') # (a, ty) # \<Gamma>')` , of e'']
    hence "(a, ty) # \<Gamma>' \<turnstile> body[x'::=e''] : \<tau>2 ; TE S a" using ih_body by auto
    hence "?inner\<Gamma> \<turnstile> body[x'::=e''] : \<tau>2 ; TE S a " .
    thus ?thesis using `a \<sharp> \<Gamma>'` by auto
  qed
  (* from L11 L12 have L1:"\<Gamma>' \<turnstile> (Lam[a:ty].(body[x'::=e''])) : ty \<rightarrow> TA0 : L; eff.TT" using c13 by auto *)
  have L21:"\<turnstile> ty \<rightarrow> TA0 : L <: T'" using c11 ` \<turnstile> TA0 <: \<tau>2` by auto
  have L22: "\<turnstile> ty \<rightarrow> \<tau>2 : L <: T'" using c11 by auto
  have L3:"(Lam[a:ty].body)[x'::=e''] = (Lam[a:ty].(body[x'::=e'']))" using Lam by auto
  have L4:"\<turnstile> eff.TT <e: F'" using `F' = TT` by auto
  thm Lam
  
  have L5:"!! Env a ty body T S x. Env \<turnstile>  (Lam [a:ty].body) : T ; TE S x \<Longrightarrow> False"
    proof -
    fix Env a ty body T S x
    assume  "Env \<turnstile>  (Lam [a:ty].body) : T ; TE S x"
    have  " Env \<turnstile>  (Lam [a:ty].body) : T ; TE S x \<Longrightarrow> False"
      by (ind_cases " Env \<turnstile>  (Lam [a:ty].body) : T ; TE S x") 
    thus False using prems by auto
  qed

  from L11 L12 L21 L22 L3 L4 L5[of \<Gamma>' a _ ty ] c13
  
  show  ?case by auto
next
  case (Iff t1 t2 t3 \<Gamma>' x' e'' T' T0' T1' F' G')
  let ?\<Gamma> = "(x', T1') # \<Gamma>'"
  have A:"(\<exists> T1 T2 T3 F1 F2 F3. 
    (?\<Gamma> \<turnstile> t1 : T1 ; F1) \<and> ?\<Gamma> |+ F1 \<turnstile> t2 : T2 ; F2 \<and> ?\<Gamma> |- F1 \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T2 <: T'  \<and> \<turnstile> T3 <: T' \<and> F' = NE)
    \<or>
    (\<exists> T1 T3 F3. (?\<Gamma> \<turnstile> t1 : T1 ; FF) \<and> ?\<Gamma> \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T3 <: T' \<and> F' = NE)
    \<or>
    (\<exists> T1 T2 F2. (?\<Gamma> \<turnstile> t1 : T1 ; TT) \<and> ?\<Gamma> \<turnstile> t2 : T2 ; F2 \<and> \<turnstile> T2 <: T'  \<and> F' = NE)" using Iff if_ty_elim by auto
  thus ?case
  proof -
    {
      assume "(\<exists> T1 T2 T3 F1 F2 F3. 
        (?\<Gamma> \<turnstile> t1 : T1 ; F1) \<and> ?\<Gamma> |+ F1 \<turnstile> t2 : T2 ; F2 \<and> ?\<Gamma> |- F1 \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T2 <: T'  \<and> \<turnstile> T3 <: T' \<and> F' = NE)"
      then obtain T1 T2 T3 F1 F2 F3 where
	"?\<Gamma> \<turnstile> t1 : T1 ; F1 "" ?\<Gamma> |+ F1 \<turnstile> t2 : T2 ; F2 "" ?\<Gamma> |- F1 \<turnstile> t3 : T3 ; F3 "" \<turnstile> T2 <: T'""\<turnstile> T3 <: T'""F' = NE"
	by auto
      hence ?thesis
      proof (nominal_induct F1 rule: eff.induct)
	case NE
	from NE have "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: NE" using Iff by auto
	then obtain S1 G1 where  A:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: NE" by auto
	have simple:"simple_eff G1" using `\<turnstile> G1 <e: NE` below_ne_simple by auto
	have p1:"(?\<Gamma> \<turnstile> t2 : T2 ; F2)" using prems by auto
	have p2:"(?\<Gamma> \<turnstile> t3 : T3 ; F3)" using prems by auto
	from p1 have "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using Iff by auto
	then obtain S2 G2 where  B:"\<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" by auto
	from p2 have "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using Iff by auto
	then obtain S3 G3 where  C:"\<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" by auto
	have B':"\<Gamma>' |+ G1 \<turnstile> t2[x'::=e''] : S2 ; G2" using B simple by auto
	have C':"\<Gamma>' |- G1 \<turnstile> t3[x'::=e''] : S3 ; G3" using C simple by auto
	have D:"\<turnstile> S2 <: T'" using prems B by auto
	have E:"\<turnstile> S3 <: T'" using prems C by auto
	from A B'  C' D E have " \<Gamma>' \<turnstile> Iff t1 t2 t3[x'::=e''] : T' ; comb_eff G1 G2 G3" by (auto simp del: comb_eff.simps)
	thus ?case using `F' = NE` by auto
      next
	case TT
	from TT have "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: TT" using Iff by auto
	then obtain S1 G1 where  A:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: TT" by auto
	have simple:"G1 = TT" using A no_sub_TT by blast
	have p1:"(?\<Gamma> \<turnstile> t2 : T2 ; F2)" using prems by auto
	have p2:"(?\<Gamma> \<turnstile> t3 : T3 ; F3)" using prems by auto
	from p1 have "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using Iff by auto
	then obtain S2 G2 where  B:"\<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" by auto
	from p2 have "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using Iff by auto
	then obtain S3 G3 where  C:"\<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" by auto
	have B':"\<Gamma>' |+ G1 \<turnstile> t2[x'::=e''] : S2 ; G2" using B simple by auto
	have C':"\<Gamma>' |- G1 \<turnstile> t3[x'::=e''] : S3 ; G3" using C simple by auto
	have D:"\<turnstile> S2 <: T'" using prems B by auto
	have E:"\<turnstile> S3 <: T'" using prems C by auto
	from A B' C' D E have " \<Gamma>' \<turnstile> Iff t1 t2 t3[x'::=e''] : T' ; comb_eff G1 G2 G3" by (auto simp del: comb_eff.simps)
	thus ?case using `F' = NE` by auto
      next
	case FF
	from FF have "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: FF" using Iff by auto
	then obtain S1 G1 where  A:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: FF" by auto
	have simple:"G1 = FF" using A no_sub_FF by blast
	have p1:"(?\<Gamma> \<turnstile> t2 : T2 ; F2)" using prems by auto
	have p2:"(?\<Gamma> \<turnstile> t3 : T3 ; F3)" using prems by auto
	from p1 have "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using Iff by auto
	then obtain S2 G2 where  B:"\<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" by auto
	from p2 have "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using Iff by auto
	then obtain S3 G3 where  C:"\<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" by auto
	have B':"\<Gamma>' |+ G1 \<turnstile> t2[x'::=e''] : S2 ; G2" using B simple by auto
	have C':"\<Gamma>' |- G1 \<turnstile> t3[x'::=e''] : S3 ; G3" using C simple by auto
	have D:"\<turnstile> S2 <: T'" using prems B by auto
	have E:"\<turnstile> S3 <: T'" using prems C by auto
	from A B' C' D E have " \<Gamma>' \<turnstile> Iff t1 t2 t3[x'::=e''] : T' ; comb_eff G1 G2 G3" by (auto simp del: comb_eff.simps)
	thus ?case using `F' = NE` by auto
      next
	case (VE z)
	hence  A:"t1 = (Var z) " "?\<Gamma> \<turnstile> Var z : T1 ; VE z"
	  using ve_ty_elim[OF `?\<Gamma> \<turnstile> t1 :  T1;  VE z`] using eff.inject by auto
	have size1:"(Var z\<guillemotleft>Iff t1 t2 t3)" using A by simp
	note Iff(1)[of "Var z"]
        hence ih_f:"!! c \<sigma> \<Gamma> T F e' T0 F0 . 
          (c,\<sigma>)#\<Gamma> \<turnstile> (Var z) : T ; F \<Longrightarrow> \<Gamma> \<turnstile> e' : T0 ; F0 \<Longrightarrow> \<turnstile> T0 <: \<sigma> \<Longrightarrow> valid ((c,\<sigma>)#\<Gamma>) \<Longrightarrow> closed e' \<Longrightarrow> e' : values
          \<Longrightarrow> EX T' F' . \<Gamma> \<turnstile> (Var z)[c::=e'] : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F" using size1 by auto
        have "EX A' Fn' . \<Gamma>' \<turnstile> (Var z)[x'::=e''] : A' ; Fn' \<and> \<turnstile> A' <: T1 \<and> \<turnstile> Fn' <e: VE z" 
           using ih_f A Iff by auto
	then obtain A' Fn' where  B:"\<Gamma>' \<turnstile> (Var z)[x'::=e''] : A' ; Fn' \<and> \<turnstile> A' <:T1" by auto
	let ?mapfun = "(%f. (% (v,ty). (if (z = v) then (v,f ty.FF ty) else (v,ty))))"
        let ?\<Gamma>1 = "(map (?mapfun remove) \<Gamma>')"
        let ?\<Gamma>2 = "(map (?mapfun replace) \<Gamma>')"          
        have "valid \<Gamma>'" using `valid ?\<Gamma>` using valid_elim[of x' T1' \<Gamma>'] by auto
	show ?case 
	proof (cases "x' = z")
	  case True
          from A True have  "(Var z)[x'::=e''] = e''" by auto
          hence D:"\<Gamma>' \<turnstile> (Var z)[x'::=e''] : T0' ; G'" "closed ((Var z)[x'::=e''])" "((Var z)[x'::=e'']) : values"
	    using Iff by auto
          have "\<turnstile> T0' <: T1'" .
          note var_ty_elim[of ?\<Gamma> z _ "VE z"]
          hence "(x', T1') : set ?\<Gamma>" using A True by auto
          have "?\<Gamma> \<turnstile> (Var x') : T1' ; VE x'" using `valid ?\<Gamma>` by auto
	  have "simple_ty T0'" using `\<Gamma>' \<turnstile> e'' : T0' ; G'` `e'' : values` value_simple_type by auto
	  let ?mapfun = "(%f. (% (v,ty). (if (z = v) then (v,f ty.FF ty) else (v,ty))))"
          let ?\<Gamma>1 = "(map (?mapfun remove) \<Gamma>')"
          let ?\<Gamma>2 = "(map (?mapfun replace) \<Gamma>')"  

          have "?\<Gamma>1 = envop remove z ty.FF \<Gamma>'" by auto
          have "?\<Gamma>2 = envop replace z ty.FF \<Gamma>'" by auto
          have "x' \<sharp> \<Gamma>'" using Iff valid_elim[of x' T1' \<Gamma>'] by auto
          hence "?\<Gamma>1 = \<Gamma>'" using True envop_forget `valid \<Gamma>'` by auto
          hence GA:"?\<Gamma> |+ VE z = (x',remove ty.FF T1') # \<Gamma>'" using True by auto
          hence G1:"\<dots> \<turnstile> t2 : T2; F2" using `(?\<Gamma> |+ VE z)\<turnstile> t2 : T2 ; F2` by auto
          have "?\<Gamma>2 = \<Gamma>'" using `x' \<sharp> \<Gamma>'` True envop_forget `valid \<Gamma>'` by auto
          hence "?\<Gamma> |- VE z = (x',replace ty.FF T1') # \<Gamma>'" using True by auto
	  hence GB:"?\<Gamma> |- VE z = (x',ty.FF) # \<Gamma>'" by auto
          hence G2:"\<dots> \<turnstile> t3 : T3; F3" using `(?\<Gamma> |- VE z)\<turnstile> t3 : T3 ; F3` by auto
          have "valid (?\<Gamma> |+ VE z)" using `valid ?\<Gamma>` envplus_valid[of ?\<Gamma> "VE z"] by auto
          hence G3:"valid ((x',remove ty.FF T1') # \<Gamma>')" using GA by auto
          have "valid (?\<Gamma> |- VE z)" using `valid ?\<Gamma>` envminus_valid[of ?\<Gamma> "VE z"] by auto
          hence G4:"valid ((x',ty.FF) # \<Gamma>')" using GB by auto        
	  show ?thesis 
	  proof (cases "e'' = Bool False")
	    case True
	    hence "(Var z)[x'::=e''] = Bool False" using `x' = z` by auto
	    hence "t1[x'::=e''] = Bool False" using `t1 = Var z` by auto
	    hence X1:"?\<Gamma> \<turnstile> t1[x'::=e''] : ty.FF ; FF" using `valid ?\<Gamma>` by auto
	    have "\<Gamma>' \<turnstile> e'' : ty.FF ; FF" using True `valid \<Gamma>'` by auto
	    note `?\<Gamma> |- VE z = (x', ty.FF) # \<Gamma>'`
	    hence "valid  ((x', ty.FF) # \<Gamma>')" using G4 by auto
	    have X2:"(x', ty.FF) # \<Gamma>' \<turnstile> t3 : T3 ; F3" using VE  `?\<Gamma> |- VE z = (x', ty.FF) # \<Gamma>'` by auto
	    note Iff(4)[ OF X2 `\<Gamma>' \<turnstile> e'' : ty.FF ; FF ` _ `valid ((x', ty.FF) # \<Gamma>')`]
	    then obtain T'' F'' where X3:"\<Gamma>' \<turnstile> t3[x'::=e''] : T'' ; F''  " and X4:" \<turnstile> T'' <: T3 "" \<turnstile> F'' <e: F3"
	      using `closed e''` `e'' : values` by auto
	    hence "\<turnstile> T'' <: T'" using `\<turnstile> T3 <: T'` by auto
	    hence "\<Gamma>' \<turnstile> Iff (Bool False) (t2[x'::=e'']) (t3[x'::=e'']) : T'' ; NE" using `valid \<Gamma>'` X3 by auto
	    hence "\<Gamma>' \<turnstile> (Iff t1 t2 t3)[x'::=e''] : T'' ; NE" using ` t1[x'::=e''] = Bool False` by auto
	    thus ?thesis  using `\<turnstile> T'' <: T'` `F' = NE` by auto
	  next
	    case False
	    hence "(Var z)[x'::=e''] = e''" using `x' = z` by auto
	    hence "t1[x'::=e''] = e''" using `t1 = Var z` by auto
	    hence X1:"\<Gamma>' \<turnstile> t1[x'::=e''] : T0' ; G'" by auto
	    have "\<Gamma>' \<turnstile> e'' : T0' ; G'" .
	    hence "G' = TT" using value_effect_tt_or_ff[OF `e'' : values` `\<Gamma>' \<turnstile> e'' : T0' ; G'`] False by auto
	    hence X2:"\<Gamma>' \<turnstile> t1[x'::=e''] : T0' ; TT" using X1 by auto
	    have "\<turnstile> T0' <: T1'" .

	    have X3:"\<not> \<turnstile> T0' <: ty.FF"
	    proof (rule ccontr)
	      assume "\<not>\<not> \<turnstile> T0' <: ty.FF"
	      hence "\<turnstile> T0' <: ty.FF" by simp
	      hence "\<turnstile> T0' <: BoolTy" using BoolTy_def by auto
	      hence "EX b. e'' = Bool b" using bool_value `e'' : values ` `\<Gamma>' \<turnstile> e'' : T0' ; G'` by auto
	      then obtain b where A:"e'' = Bool b" by auto
	      thus False
	      proof (cases b)
		case False
		thus ?thesis using A `e'' ~= Bool False` by auto
	      next
		case True
		hence "T0' = ty.TT" using  `\<Gamma>' \<turnstile> e'' : T0' ; G'` A true_ty_elim by auto
		thus ?thesis using `\<turnstile> T0' <: ty.FF` tt_sub_ff by auto
	      qed
	    qed


	    
	    let ?rty = "remove ty.FF T1'"

	    note `?\<Gamma> |+ VE z = (x', ?rty) # \<Gamma>'`
	    hence "valid  ((x',  ?rty) # \<Gamma>')" using G3 by auto
	    have X2:"(x', ?rty) # \<Gamma>' \<turnstile> t2 : T2 ; F2" using VE  `?\<Gamma> |+ VE z = (x', ?rty) # \<Gamma>'` by auto
	    note Iff(3)[ OF X2 `\<Gamma>' \<turnstile> e'' : T0'  ; G' ` _ `valid ((x', ?rty) # \<Gamma>')`]
	    then obtain T'' F'' where X3:"\<Gamma>' \<turnstile> t2[x'::=e''] : T'' ; F''  " and X4:" \<turnstile> T'' <: T2 "" \<turnstile> F'' <e: F2"
	      using `closed e''` `e'' : values` remove_soundness[OF `\<turnstile> T0' <: T1'` X3 `simple_ty T0'`] by auto
	    hence "\<turnstile> T'' <: T'" using `\<turnstile> T2 <: T'` by auto
	    hence "\<Gamma>' \<turnstile> Iff e'' (t2[x'::=e'']) (t3[x'::=e'']) : T'' ; NE" using `valid \<Gamma>'` X3  `\<Gamma>' \<turnstile> e'' : T0'  ; G' ` 
	      `G' = TT` by auto
	    hence "\<Gamma>' \<turnstile> (Iff t1 t2 t3)[x'::=e''] : T'' ; NE" using ` t1[x'::=e''] = e''` by auto
	    thus ?thesis  using `\<turnstile> T'' <: T'` `F' = NE` by auto
	    
	  qed
	next
	  case False
	  from A False have "(Var z)[x'::=e''] = (Var z)" by auto
	  hence D:"\<Gamma>' \<turnstile> (Var z)[x'::=e''] : T1 ; VE z" using False A 
          proof -
            have q1:"?\<Gamma> \<turnstile> Var z : T1 ; VE z" using A by auto
            have "x' \<sharp> Var z" using trm.fresh False fresh_atm by auto
            hence "\<Gamma>' \<turnstile> Var z : T1 ; VE z" using q1 fresh_weakening_cons `valid ((x',T1')# \<Gamma>')` by auto
            thus ?thesis using `(Var z)[x'::=e''] = Var z` by auto
          qed
          hence typetst: "\<Gamma>' \<turnstile> t1[x'::=e''] : T1 ; VE z" using A by auto
	  have F:"?\<Gamma> |+ VE z = (x',T1') # ?\<Gamma>1" using False by auto
          hence H:"(x',T1') # ?\<Gamma>1 \<turnstile> t2 : T2 ; F2" using `?\<Gamma> |+ VE z \<turnstile> t2 : T2 ; F2` by auto
          hence K:"valid ?\<Gamma>1" using envop_valid `valid \<Gamma>'` by auto
          have J:"?\<Gamma>1 \<turnstile> e'' : T0' ; G'" using K `valid \<Gamma>'` closed_any_env `closed e''` Iff by blast
          have "x' \<sharp> ?\<Gamma>1" using Iff valid_elim[of x' T1' \<Gamma>'] envop_fresh[of x' \<Gamma>' remove] `valid \<Gamma>'` by auto
          hence "valid ((x',T1')#?\<Gamma>1)" using `valid ?\<Gamma>1` by auto
          hence ex1:"\<exists>S2 G2. ?\<Gamma>1  \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2"
            using H J K Iff by auto 

	  have G:"?\<Gamma> |- VE z = (x',T1') # ?\<Gamma>2" using False by auto
          hence H:"(x',T1') # ?\<Gamma>2 \<turnstile> t3 : T3 ; F3" using `?\<Gamma> |- VE z \<turnstile> t3 : T3 ; F3` by auto
          hence K:"valid ?\<Gamma>2" using envop_valid `valid \<Gamma>'` by auto
          have J:"?\<Gamma>2 \<turnstile> e'' : T0' ; G'" using K `valid \<Gamma>'` closed_any_env `closed e''` Iff by blast
          have "x' \<sharp> ?\<Gamma>2" using Iff valid_elim[of x' T1' \<Gamma>'] envop_fresh[of x' \<Gamma>' _ z _] `valid \<Gamma>'` by auto
          hence "valid ((x',T1')#?\<Gamma>2)" using `valid ?\<Gamma>2` by auto
          hence ex2:"\<exists>S3 G3. ?\<Gamma>2  \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3"
            using H J K Iff by auto

          from ex1 obtain S2 G2 where 1:"?\<Gamma>1  \<turnstile> t2[x'::=e''] : S2 ; G2"" \<turnstile> S2 <: T'" using `\<turnstile> T2 <: T'` by auto
          from ex2 obtain S3 G3 where 2:"?\<Gamma>2  \<turnstile> t3[x'::=e''] : S3 ; G3"" \<turnstile> S3 <: T'" using `\<turnstile> T3 <: T'`  by auto
          have 4:"?\<Gamma>1 = \<Gamma>' |+ (VE z)" by auto
          have 5:"?\<Gamma>2 = \<Gamma>' |- (VE z)" by auto
          have X:"!! G G' e T F. G = G' \<Longrightarrow> G \<turnstile> e : T ; F \<Longrightarrow> G' \<turnstile> e : T ; F" by auto
          from 1 4 have 6:"\<Gamma>' |+ (VE z) \<turnstile> t2[x'::=e''] : S2 ; G2" using X[of ?\<Gamma>1 "\<Gamma>' |+ (VE z)" " t2[x'::=e'']" S2 G2]
            by blast
          from 2 5 have 7:"\<Gamma>' |- (VE z) \<turnstile> t3[x'::=e''] : S3 ; G3" using X[of ?\<Gamma>2 "\<Gamma>' |- (VE z)" " t3[x'::=e'']" S3 G3]
            by blast
          
          from typetst 1 2 6 7 have "\<Gamma>' \<turnstile> (Iff t1 t2 t3)[x'::=e''] : T' ; comb_eff (VE z) G2 G3" by (auto simp del: comb_eff.simps)
	  thus ?thesis  using `F' = NE` by auto
	qed
      next
	case (TE U z)
	have "EX f A A1 Fn B. t1 = (App f (Var z)) \<and> (x', T1') # \<Gamma>' \<turnstile> f : B ; Fn \<and> \<turnstile> B <: A1 \<rightarrow> T1 : Latent U \<and>
	  (x', T1') # \<Gamma>' \<turnstile> (Var z) : A ; VE z \<and> \<turnstile> A <: A1" 
          using TE te_ty_elim[of ?\<Gamma> t1 T1 U z] by auto
	then obtain f A1 A Fn B where A:"t1 = (App f (Var z)) "" (x', T1') # \<Gamma>' \<turnstile> f : B ; Fn" "\<turnstile> B <: A1 \<rightarrow> T1 : Latent U"
	  "(x', T1') # \<Gamma>' \<turnstile> (Var z) : A ; VE z "" \<turnstile> A <: A1" by auto
	have size1:"(f\<guillemotleft>Iff t1 t2 t3)" using A(1) by (simp )
	note Iff(1)[of f]
        hence ih_f:"!! c \<sigma> \<Gamma> T F e' T0 F0 . 
          (c,\<sigma>)#\<Gamma> \<turnstile> f : T ; F \<Longrightarrow> \<Gamma> \<turnstile> e' : T0 ; F0 \<Longrightarrow> \<turnstile> T0 <: \<sigma> \<Longrightarrow> valid ((c,\<sigma>)#\<Gamma>) \<Longrightarrow> closed e' \<Longrightarrow> e' : values
          \<Longrightarrow> EX T' F' . \<Gamma> \<turnstile> f[c::=e'] : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F" using size1 by auto
        have "EX A' Fn' . \<Gamma>' \<turnstile> f[x'::=e''] : A' ; Fn' \<and> \<turnstile> A' <: B \<and> \<turnstile> Fn' <e: Fn" 
          using ih_f A Iff by auto
	then obtain A' Fn' where  B:"\<Gamma>' \<turnstile> f[x'::=e''] : A' ; Fn' \<and> \<turnstile> A' <:B" by auto
	let ?mapfun = "(%f. (% (v,ty). (if (z = v) then (v,f U ty) else (v,ty))))"
        let ?\<Gamma>1 = "(map (?mapfun restrict) \<Gamma>')"
        let ?\<Gamma>2 = "(map (?mapfun remove) \<Gamma>')"          
        have "valid \<Gamma>'" using `valid ?\<Gamma>` using valid_elim[of x' T1' \<Gamma>'] by auto

	show ?case 
	proof (cases "x' = z")
	  case True
          from A True have  "(Var z)[x'::=e''] = e''" by auto
          hence D:"\<Gamma>' \<turnstile> (Var z)[x'::=e''] : T0' ; G'" "closed ((Var z)[x'::=e''])" "((Var z)[x'::=e'']) : values"
	    using Iff by auto
          have "\<turnstile> T0' <: T1'" .
          note var_ty_elim[of ?\<Gamma> z A "VE z"]
          hence "(x', A) : set ?\<Gamma>" using A True by auto
          have "?\<Gamma> \<turnstile> (Var x') : T1' ; VE x'" using `valid ?\<Gamma>` by auto
          hence "T1' = A" using A unique_var_typing[of ] True by auto
          have "\<turnstile> T0' <: T1'" .
          hence "\<turnstile> T0' <: A" using `T1' = A` by simp
	  have "simple_ty T0'" using `\<Gamma>' \<turnstile> e'' : T0' ; G'` `e'' : values` value_simple_type by auto
          have or:"
            (\<turnstile> T0' <: U \<and> \<turnstile> T0' <: restrict U T1') \<or>
            (~ (\<turnstile> T0' <: U)  \<and> \<turnstile> T0' <: remove U T1')" 
            using `\<Gamma>' \<turnstile> e'' : T0' ; G'` `e'' : values` `\<turnstile> T0' <: T1'` `closed e''` `simple_ty T0'`
            restrict_remove_soundness
            by auto
          have "?\<Gamma>1 = envop restrict z U \<Gamma>'" by auto
          have "?\<Gamma>2 = envop remove z U \<Gamma>'" by auto
          have "x' \<sharp> \<Gamma>'" using Iff valid_elim[of x' T1' \<Gamma>'] by auto
          hence "?\<Gamma>1 = \<Gamma>'" using True envop_forget `valid \<Gamma>'` by auto
          hence GA:"?\<Gamma> |+ TE U z = (x',restrict U T1') # \<Gamma>'" using True by auto
          hence G1:"\<dots> \<turnstile> t2 : T2; F2" using `(?\<Gamma> |+ TE U z)\<turnstile> t2 : T2 ; F2` by auto
          have "?\<Gamma>2 = \<Gamma>'" using `x' \<sharp> \<Gamma>'` True envop_forget `valid \<Gamma>'` by auto
          hence GB:"?\<Gamma> |- TE U z = (x',remove U T1') # \<Gamma>'" using True by auto
          hence G2:"\<dots> \<turnstile> t3 : T3; F3" using `(?\<Gamma> |- TE U z)\<turnstile> t3 : T3 ; F3` by auto
          have "valid (?\<Gamma> |+ TE U z)" using `valid ?\<Gamma>` envplus_valid[of ?\<Gamma> "TE U z"] by auto
          hence G3:"valid ((x',restrict U T1') # \<Gamma>')" using GA by auto
          have "valid (?\<Gamma> |- TE U z)" using `valid ?\<Gamma>` envminus_valid[of ?\<Gamma> "TE U z"] by auto
          hence G4:"valid ((x',remove U T1') # \<Gamma>')" using GB by auto
          show ?thesis
          proof -
            {
              assume "\<turnstile> T0' <: U "" \<turnstile> T0' <: restrict U T1'"
              have 2:"(x', restrict U T1') # \<Gamma>' \<turnstile> t2 : T2 ; F2 " using `?\<Gamma> |+ TE U z \<turnstile> t2 : T2 ; F2` GA by auto
              note Iff(2)[of x' "restrict U T1'" \<Gamma>' T2 F2 e'' T0' G'] 
              hence "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using G3 prems `closed e''` 2 by auto
              then obtain S2 G2 where L1:"\<Gamma>'|+ eff.TT \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" by auto
              have "\<turnstile> T0' <: A1" "\<turnstile> A' <:  A1 \<rightarrow> T1 : Latent U" using A B D `\<turnstile> T0' <: A` by auto
              hence "\<Gamma>' \<turnstile> (App f (Var z))[x'::=e''] : T1 ; eff.TT" using A B D `\<turnstile> T0' <: A` `\<turnstile> T0' <: U` 
		using T_AppPredTrue[of \<Gamma>' _ A' Fn' A1 T1 U _ T0' G'] by auto
              hence L3:"\<Gamma>' \<turnstile> t1[x'::=e''] : T1 ; eff.TT" using `t1 = App f (Var z)` by auto
              have "\<turnstile> S2 <: T'"  using L1 `\<turnstile> T2 <: T'` by auto
              hence "\<Gamma>'\<turnstile> (Iff t1 t2 t3)[x'::=e''] : T' ; eff.NE"
                using L3 ` \<Gamma>'|+eff.TT \<turnstile> t2[x'::=e''] : S2 ; G2` by auto
              hence ?thesis using `F' = NE` by auto              
            }
            moreover
            {
              assume "~ (\<turnstile> T0' <: U) "" \<turnstile> T0' <: remove U T1'"
              have 3:"(x', remove U T1') # \<Gamma>' \<turnstile> t3 : T3 ; F3 " using `?\<Gamma> |- TE U z \<turnstile> t3 : T3 ; F3` GB by auto
              note Iff(3)[of x' "remove U T1'" \<Gamma>' T3 F3 e'' T0' G'] 
              hence "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using G4 prems `closed e''` 3 by auto
              then obtain S3 G3 where L1:"\<Gamma>'|+ eff.FF \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" by auto
              have "\<turnstile> T0' <: A1" using A B D `\<turnstile> T0' <: A` by auto
              hence "\<Gamma>' \<turnstile> (App f (Var z))[x'::=e''] : T1 ; eff.FF" using A B D `\<turnstile> T0' <: A` `~ (\<turnstile> T0' <: U)` 
		using T_AppPredFalse[of \<Gamma>' _ A' Fn' A1 T1 U _ T0' G'] by auto
              hence L3:"\<Gamma>' \<turnstile> t1[x'::=e''] : T1 ; eff.FF" using `t1 = App f (Var z)` by auto
              have "\<turnstile> S3 <: T'"  using L1 `\<turnstile> T3 <: T'` by auto
              hence "\<Gamma>'\<turnstile> (Iff t1 t2 t3)[x'::=e''] : T' ; eff.NE"
                using L3 ` \<Gamma>'|+eff.FF \<turnstile> t3[x'::=e''] : S3 ; G3` by auto
              hence ?thesis using `F' = NE` by auto              
            }
            ultimately show ?thesis using or by auto
          qed
	next
	  case False
	  from A False have "(Var z)[x'::=e''] = (Var z)" by auto
	  hence D:"\<Gamma>' \<turnstile> (Var z)[x'::=e''] : A ; VE z" using False A
          proof -
            have q1:"?\<Gamma> \<turnstile> Var z : A ; VE z" .
            have "x' \<sharp> Var z" using trm.fresh False fresh_atm by auto
            hence "\<Gamma>' \<turnstile> Var z : A ; VE z" using q1 fresh_weakening_cons `valid ((x',T1')# \<Gamma>')` by auto
            thus ?thesis using `(Var z)[x'::=e''] = Var z` by auto
          qed
	  from A B D have "\<Gamma>' \<turnstile> App (f[x'::=e'']) ((Var z)[x'::=e'']) : T1 ; TE U z" by auto
          hence typetst: "\<Gamma>' \<turnstile> t1[x'::=e''] : T1 ; TE U z" using A by auto
	  have F:"?\<Gamma> |+ TE U z = (x',T1') # ?\<Gamma>1" using False by auto
          hence H:"(x',T1') # ?\<Gamma>1 \<turnstile> t2 : T2 ; F2" using `?\<Gamma> |+ TE U z \<turnstile> t2 : T2 ; F2` by auto
          hence K:"valid ?\<Gamma>1" using envop_valid `valid \<Gamma>'` by auto
          have J:"?\<Gamma>1 \<turnstile> e'' : T0' ; G'" using K `valid \<Gamma>'` closed_any_env `closed e''` Iff by blast
          have "x' \<sharp> ?\<Gamma>1" using Iff valid_elim[of x' T1' \<Gamma>'] envop_fresh[of x' \<Gamma>' restrict z U] `valid \<Gamma>'` by auto
          hence "valid ((x',T1')#?\<Gamma>1)" using `valid ?\<Gamma>1` by auto
          hence ex1:"\<exists>S2 G2. ?\<Gamma>1  \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2"
            using H J K Iff by auto 

	  have G:"?\<Gamma> |- TE U z = (x',T1') # ?\<Gamma>2" using False by auto
          hence H:"(x',T1') # ?\<Gamma>2 \<turnstile> t3 : T3 ; F3" using `?\<Gamma> |- TE U z \<turnstile> t3 : T3 ; F3` by auto
          hence K:"valid ?\<Gamma>2" using envop_valid `valid \<Gamma>'` by auto
          have J:"?\<Gamma>2 \<turnstile> e'' : T0' ; G'" using K `valid \<Gamma>'` closed_any_env `closed e''` Iff by blast
          have "x' \<sharp> ?\<Gamma>2" using Iff valid_elim[of x' T1' \<Gamma>'] envop_fresh[of x' \<Gamma>' remove z U] `valid \<Gamma>'` by auto
          hence "valid ((x',T1')#?\<Gamma>2)" using `valid ?\<Gamma>2` by auto
          hence ex2:"\<exists>S3 G3. ?\<Gamma>2  \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3"
            using H J K Iff by auto

          from ex1 obtain S2 G2 where 1:"?\<Gamma>1  \<turnstile> t2[x'::=e''] : S2 ; G2"" \<turnstile> S2 <: T'" using `\<turnstile> T2 <: T'` by auto
          from ex2 obtain S3 G3 where 2:"?\<Gamma>2  \<turnstile> t3[x'::=e''] : S3 ; G3"" \<turnstile> S3 <: T'" using `\<turnstile> T3 <: T'`  by auto
          have 4:"?\<Gamma>1 = \<Gamma>' |+ (TE U z)" by auto
          have 5:"?\<Gamma>2 = \<Gamma>' |- (TE U z)" by auto
          have X:"!! G G' e T F. G = G' \<Longrightarrow> G \<turnstile> e : T ; F \<Longrightarrow> G' \<turnstile> e : T ; F" by auto
          from 1 4 have 6:"\<Gamma>' |+ (TE U z) \<turnstile> t2[x'::=e''] : S2 ; G2" using X[of ?\<Gamma>1 "\<Gamma>' |+ (TE U z)" " t2[x'::=e'']" S2 G2]
            by blast
          from 2 5 have 7:"\<Gamma>' |- (TE U z) \<turnstile> t3[x'::=e''] : S3 ; G3" using X[of ?\<Gamma>2 "\<Gamma>' |- (TE U z)" " t3[x'::=e'']" S3 G3]
            by blast
          
          from typetst 1 2 6 7 have "\<Gamma>' \<turnstile> (Iff t1 t2 t3)[x'::=e''] : T' ; comb_eff (TE U z) G2 G3" by (auto simp del: comb_eff.simps)
	  thus ?thesis  using `F' = NE` by auto
	qed
      qed
    }
    moreover
    {
      assume "\<exists> T1 T3 F3. (?\<Gamma> \<turnstile> t1 : T1 ; FF) \<and> ?\<Gamma> \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T3 <: T' \<and> F' = NE"
      then obtain T1 T3 F3 where "?\<Gamma> \<turnstile> t1 : T1 ; FF" "?\<Gamma> \<turnstile> t3 : T3 ; F3" "\<turnstile> T3 <: T'" "F' = NE"
	by auto
      hence "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: FF" using Iff by auto
      then obtain S1 G1 where B:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: FF" by auto
      hence  C:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; FF  " using B no_sub_FF by auto
      from prems have "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using Iff by auto
      then obtain S3 G3 where D:"\<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3 ""\<turnstile> S3 <: T3" by auto
      from B C D have "\<Gamma>' \<turnstile> (Iff  (t1[x'::=e'']) (t2[x'::=e'']) (t3[x'::=e''])) : S3 ; eff.NE" by auto
      hence ?thesis  using `\<turnstile> T3 <: T'` `\<turnstile> S3 <: T3` `F' = NE` by auto
    }
    moreover
    {
      assume "\<exists> T1 T2 F2. (?\<Gamma> \<turnstile> t1 : T1 ; TT) \<and> ?\<Gamma> \<turnstile> t2 : T2 ; F2 \<and> \<turnstile> T2 <: T'  \<and> F' = NE"
      then obtain T1 T2 F2 where "?\<Gamma> \<turnstile> t1 : T1 ; TT" "?\<Gamma> \<turnstile> t2 : T2 ; F2" "\<turnstile> T2 <: T'" "F' = NE"
	by auto
      hence "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: TT" using Iff by auto
      then obtain S1 G1 where B:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: TT" by auto
      hence  C:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; TT  " using B no_sub_TT by auto
      from prems have "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using Iff by auto
      then obtain S2 G2 where D:"\<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2 ""\<turnstile> S2 <: T2" by auto
      from B C D have "\<Gamma>' \<turnstile> (Iff  (t1[x'::=e'']) (t2[x'::=e'']) (t3[x'::=e''])) : S2 ; eff.NE" by auto
      hence ?thesis  using `\<turnstile> T2 <: T'` `\<turnstile> S2 <: T2` `F' = NE` by auto
    }
    ultimately show ?thesis using A by blast
  qed
qed

lemma subst_produces_TT:
  assumes ty:"(x,T0)#\<Gamma> \<turnstile> e : T ; TE S x"
  and vty:"\<Gamma> \<turnstile> v : T0' ; F"
  and A:"\<turnstile> T0' <: T0"
  and B:"valid ((x,T0)#\<Gamma>)" 
  and C:"closed v" and D:"v : values"
  and E:"\<turnstile> T0' <: S"
  shows "EX T'. \<Gamma> \<turnstile> e[x::=v] : T' ; TT \<and> \<turnstile> T' <: T"
proof -
  obtain f A A1 Fn Sa B
    where
    eq:"e = App f (Var x)" and fty:"(x, T0) # \<Gamma> \<turnstile> f : B ; Fn  "
    and bsub:" \<turnstile> B <: A1 \<rightarrow> T : Latent S " and xty:" (x, T0) # \<Gamma> \<turnstile> Var x : A ; VE x  "
    and asub:" \<turnstile> A <: A1"
    using te_ty_elim[OF ty] by auto
  note preserve_subst[OF fty vty A B C D]
  then obtain T' F' where
    X1:"\<Gamma> \<turnstile> f[x::=v] : T' ; F'  " and " \<turnstile> T' <: B "" \<turnstile> F' <e: Fn"
    by auto
  hence X2:"\<turnstile> T' <: A1 \<rightarrow> T : Latent S" using bsub by auto
  have "(Var x)[x::=v] = v" by simp
  hence X3:"\<Gamma> \<turnstile> (Var x)[x::=v] : T0' ; F" using vty by auto
  have "(x, T0) # \<Gamma> \<turnstile> Var x : T0 ; VE x" using `valid ((x, T0) # \<Gamma>)` by auto
  hence "T0 = A" using xty unique_var_typing by auto
  hence "\<turnstile> T0' <: A1" using A asub by auto
  from X1 X2 X3 show ?thesis using T_AppPredTrue[OF X1 X2 X3 `\<turnstile> T0' <: A1` E] using  asub E eq 
    by auto
qed
  

lemma subst_produces_FF:
  assumes ty:"(x,T0)#\<Gamma> \<turnstile> e : T ; TE S x"
  and vty:"\<Gamma> \<turnstile> v : T0' ; F"
  and A:"\<turnstile> T0' <: T0"
  and B:"valid ((x,T0)#\<Gamma>)" 
  and C:"closed v" and D:"v : values"
  and E:"~ \<turnstile> T0' <: S"
  shows "EX T'. \<Gamma> \<turnstile> e[x::=v] : T' ; FF \<and> \<turnstile> T' <: T"
proof -
  obtain f A A1 Fn Sa B
    where
    eq:"e = App f (Var x)" and fty:"(x, T0) # \<Gamma> \<turnstile> f : B ; Fn  "
    and bsub:" \<turnstile> B <: A1 \<rightarrow> T : Latent S " and xty:" (x, T0) # \<Gamma> \<turnstile> Var x : A ; VE x  "
    and asub:" \<turnstile> A <: A1"
    using te_ty_elim[OF ty] by auto
  note preserve_subst[OF fty vty A B C D]
  then obtain T' F' where
    X1:"\<Gamma> \<turnstile> f[x::=v] : T' ; F'  " and " \<turnstile> T' <: B "" \<turnstile> F' <e: Fn"
    by auto
  hence X2:"\<turnstile> T' <: A1 \<rightarrow> T : Latent S" using bsub by auto
  have veq:"(Var x)[x::=v] = v" by simp
  hence X3:"\<Gamma> \<turnstile> (Var x)[x::=v] : T0' ; F" using vty by auto
  have "(x, T0) # \<Gamma> \<turnstile> Var x : T0 ; VE x" using `valid ((x, T0) # \<Gamma>)` by auto
  hence "T0 = A" using xty unique_var_typing by auto
  hence "\<turnstile> T0' <: A1" using A asub by auto
  from X1 X2 X3 show ?thesis using T_AppPredFalse[OF X1 X2 X3 `\<turnstile> T0' <: A1` E] using  asub E eq C D veq
    by auto
qed

inductive_cases beta_cases:"App (Abs x b T) v \<hookrightarrow> e "

inductive_cases beta_TT_cases:"\<Gamma> \<turnstile> App (Abs x b T) v : T' ; TT"
inductive_cases beta_FF_cases:"\<Gamma> \<turnstile> App (Abs x b T) v : T' ; FF"

lemma preserve_red:
  assumes typed:"\<Gamma> \<turnstile> e : t ; eff" and cl:"closed e"
  and red:"e \<hookrightarrow> e'" and val:"valid \<Gamma>"
  shows "EX t' eff'. \<Gamma> \<turnstile> e' : t' ; eff' \<and> \<turnstile> t' <: t \<and> \<turnstile> eff' <e: eff "
  using red typed cl val red
  proof (nominal_induct e e' avoiding: \<Gamma> t rule: reduce.strong_induct)
    case (e_delta v' p v \<Gamma> T)
    thm app_ty_elim[of \<Gamma> "(BI p)" v' T eff]
    hence "\<exists>T0 T0' T1 le eff' eff'' U.  \<Gamma> \<turnstile> BI p : U ; eff'  \<and>  \<Gamma> \<turnstile> v' : T0' ; eff''  \<and> \<turnstile> U <: T0 \<rightarrow> T1 : le 
      \<and> \<turnstile> T0' <: T0 \<and> T1 = T"
      using app_ty_elim[of \<Gamma> "(BI p)" v' T eff] by simp
    then obtain T0 T0' T1 le eff' eff'' U where 
      A1:" \<Gamma> \<turnstile> BI p : U ; eff'" and  A2:"\<Gamma> \<turnstile> v' : T0' ; eff''" and A3:"\<turnstile> T0' <: T0"
      and A4:"T1 = T" and A5:"\<turnstile> U <: T0 \<rightarrow> T1 : le"
      by auto
    hence "U = \<Delta>\<^isub>\<tau> p" using e_delta typing_bi[of \<Gamma> p  _ eff'] by simp
    then obtain A0 A1 LA where "\<Delta>\<^isub>\<tau> p = A0 \<rightarrow> A1 : LA" "U = A0 \<rightarrow> A1 : LA" by (nominal_induct p rule: builtin.induct) auto
    hence "\<turnstile> A0 \<rightarrow> A1 : LA <: T0 \<rightarrow> T1 : le" using `\<turnstile> U <: T0 \<rightarrow> T1 : le` by auto
    hence B:"le = LA \<or> le = latent_eff.NE" "\<turnstile> T0 <: A0" "\<turnstile> A1 <: T1" using arr_sub_arr_cases[of A0 A1 LA T0 T1 le] by auto
    have C1:" \<Gamma> \<turnstile> App (BI p) v' : T1 ; eff" using prems `T1 = T` by auto
    have C2:"\<turnstile> T0' <: A0" and C3:"\<turnstile> A1 <: T " using B A3 A4 by auto
    have C4:"valid \<Gamma>" .
    note delta_soundness[OF `\<Delta>\<^isub>\<tau> p = A0 \<rightarrow> A1 : LA` `v' : values` `\<Gamma> \<turnstile> v' : T0' ; eff''` C2 e_delta(3) C3 `\<Delta> p v' = Some v` C4]
    then obtain A1' eff' where "\<Gamma> \<turnstile> v : A1' ; eff' "" \<turnstile> eff' <e: eff" "\<turnstile> A1' <: A1" by auto
    thus ?case using C3 by auto
  next
    case (e_if_false thn els \<Gamma>' t') 
    have "eff = NE" using if_false_ty_elim[of _ _ _ _ eff] e_if_false by auto
    have " \<exists>T0 eff'.  \<Gamma>' \<turnstile> els : T0 ; eff'  \<and> \<turnstile> T0 <: t' " using   if_false_ty_elim[of \<Gamma>' thn els t' eff] e_if_false by auto
    then obtain T0 eff' where  f:"\<Gamma>' \<turnstile> els : T0 ; eff'"  and g:"\<turnstile> T0 <: t'" by auto
    have "closed els" using e_if_false closed_def trm.supp by auto
    hence "simple_eff eff'" using closed_eff f by auto
    hence h:"\<turnstile> eff' <e: eff" using simple_eff_below_ne `eff = NE` by auto
    thus ?case using f g  by auto
  next
    case (e_if_true v thn els \<Gamma>' t') 
    have "eff = NE" using if_true_ty_elim[of \<Gamma>' v thn els _ eff] e_if_true by auto
    have " \<exists>T0 eff'.  \<Gamma>' \<turnstile> thn : T0 ; eff'  \<and> \<turnstile> T0 <: t' " using   if_true_ty_elim[of \<Gamma>' v thn els t' eff] e_if_true by auto
    then obtain T0 eff' where  f:"\<Gamma>' \<turnstile> thn : T0 ; eff'"  and g:"\<turnstile> T0 <: t'" by auto
    have "closed thn" using e_if_true closed_def trm.supp by auto
    hence "simple_eff eff'" using closed_eff f by auto
    hence h:"\<turnstile> eff' <e: eff" using `eff = NE` by auto
    thus ?case using f g  by auto
  next
    case (e_beta v x T b \<Gamma>' T')
    hence "simple_eff eff" using closed_eff by auto
    thm app_ty_elim[of \<Gamma>' "(Lam[x:T].b)" v t eff]
    (* hence "eff = NE" using app_abs_ty_elim_eff by auto *)
    from e_beta have "\<exists>T0 T0' T1 le eff' eff'' U.  \<Gamma>' \<turnstile> Abs x b T : U ; eff'  \<and>  \<Gamma>' \<turnstile> v : T0' ; eff''  
      \<and> \<turnstile> T0' <: T0 \<and> T1 = T' \<and> \<turnstile> U <: T0 \<rightarrow> T1 : le"
      using app_ty_elim[of \<Gamma>' "Abs x b T" v T' eff] by blast
    then obtain T0 T0' T1 le eff' eff'' U where " \<Gamma>' \<turnstile> Lam[x:T].b :U; eff'" and "\<Gamma>' \<turnstile> v : T0' ; eff''" 
      and "\<turnstile> T0' <: T0" and "T1 = T'"  and usub:"\<turnstile> U <:  T0 \<rightarrow> T1 : le " by auto
    hence "\<exists>T1a eff2 L S.  (x,T)#\<Gamma>' \<turnstile> b : T1a ; eff2 \<and> U = T \<rightarrow> T1a : L \<and> (L = Latent S \<and> eff2 = TE S x \<or> L = latent_eff.NE)"
      using abs_ty_elim[of \<Gamma>' x b T "U" eff'] e_beta `x \<sharp> \<Gamma>'` by auto
    then obtain T1a eff2 L S where  bty:"(x,T)#\<Gamma>' \<turnstile> b : T1a ; eff2" and ueq:"U = T \<rightarrow> T1a : L"
      and "(L = Latent S \<and> eff2 = TE S x \<or> L = latent_eff.NE)"
      by auto
    have "closed v" using e_beta closed_def trm.supp by auto
    have "v : values" using e_beta beta_cases[of _ _ _ v _ "v : values"]  trm.inject by auto
    have "\<turnstile> T0 <: T" using usub ueq arr_sub_arr_cases[of T T1a L T0 T1 le] by auto
    have "\<turnstile> T1a <: T1" using usub ueq arr_sub_arr_cases[of T T1a L T0 T1 le] by auto
    hence "\<turnstile> T1a <: T'" using `T1 = T'` by simp
    have "\<turnstile> T0' <: T" using ` \<turnstile> T0' <: T0` `\<turnstile>T0<:T` by auto
    have " \<exists>T'a F'.  \<Gamma>' \<turnstile> b[x::=v] : T'a ; F'  \<and> \<turnstile> T'a <: T1a"
      using preserve_subst[of x T \<Gamma>' b T1a eff2 v T0' eff''] `\<Gamma>' \<turnstile> v : T0' ; eff''` bty `\<turnstile> T0' <: T` `x \<sharp> \<Gamma>'` `valid \<Gamma>'` 
      `closed v` `v : values`
      by auto
    then obtain T'a F' where a:"\<Gamma>' \<turnstile> b[x::=v] : T'a ; F'" and b:"\<turnstile> T'a <: T1a" by auto
    have "closed (b[x::=v])" using e_beta reduce_closed by blast
    hence c:"simple_eff F'" using a closed_eff by auto
    have ?case using `simple_eff eff` e_beta a b

    proof (induct eff rule: simple_eff_cases)
      case NE thus ?case using simple_eff_below_ne[of F'] c a b `\<turnstile> T1a <: T'` by auto
    next
      case TT
      obtain U T0 Ta S eff1 eff2 where  X1:"\<Gamma>' \<turnstile> (Lam [x:T].b) : U ; eff1 " and X2:"\<turnstile> U <: T0 \<rightarrow> T' : Latent S" and
	X3:" \<Gamma>' \<turnstile> v : Ta ; eff2 " "\<turnstile> Ta <: T0"" \<turnstile> Ta <: S"
	using trm.inject  beta_TT_cases[OF TT(5), of thesis]
	by auto
      note abs_ty_elim[OF X1 `x \<sharp> \<Gamma>'`]
      then obtain T1' eff' L S' where f:
	"(x, T) # \<Gamma>' \<turnstile> b : T1' ; eff'  "
	" U = T \<rightarrow> T1' : L "
	" eff1 = eff.TT "
	" (eff' = TE S' x \<and> L = Latent S' \<or> L = latent_eff.NE)" 
	by auto
      hence "eff' = TE S x" "\<turnstile> T0 <: T" "\<turnstile> T1' <: T'"using `U = T \<rightarrow> T1' : L` X2 using arr_sub_arr_cases[of T T1' L T0 T' "Latent S"] 
	by auto
      hence X4:"(x, T) # \<Gamma>' \<turnstile> b : T1' ; TE S x" using f by auto
      have valcons:"valid ((x,T)#\<Gamma>')" using `valid \<Gamma>'` `x \<sharp> \<Gamma>'` by auto
      have "\<turnstile> Ta <: T" using `\<turnstile> Ta <: T0``\<turnstile> T0 <: T`  by auto
      have "EX T2'. \<Gamma>' \<turnstile> b[x::=v] : T2' ; TT \<and> \<turnstile> T2' <: T1'" using X3 
	using subst_produces_TT[OF X4 `\<Gamma>' \<turnstile> v : Ta ; eff2` `\<turnstile> Ta <: T` valcons ` closed v`` v \<in> values` `\<turnstile> Ta <: S`] 
	by auto
      
      thus ?case using `\<turnstile> T1' <: T'` by auto
    next
      case FF
      obtain U T0 Ta S eff1 eff2 where  X1:"\<Gamma>' \<turnstile> (Lam [x:T].b) : U ; eff1 " and X2:"\<turnstile> U <: T0 \<rightarrow> T' : Latent S" and
	X3:" \<Gamma>' \<turnstile> v : Ta ; eff2 " "\<turnstile> Ta <: T0""~ \<turnstile> Ta <: S"
	using trm.inject  beta_FF_cases[OF FF(5), of thesis]
	by auto
      note abs_ty_elim[OF X1 `x \<sharp> \<Gamma>'`]
      then obtain T1' eff' L S' where f:
	"(x, T) # \<Gamma>' \<turnstile> b : T1' ; eff'  "
	" U = T \<rightarrow> T1' : L "
	" eff1 = eff.TT "
	" (eff' = TE S' x \<and> L = Latent S' \<or> L = latent_eff.NE)" 
	by auto
      hence "eff' = TE S x"  "\<turnstile> T0 <: T" "\<turnstile> T1' <: T'" using `U = T \<rightarrow> T1' : L` X2 using arr_sub_arr_cases[of T T1' L T0 T' "Latent S"] 
	by auto
      hence X4:"(x, T) # \<Gamma>' \<turnstile> b : T1' ; TE S x" using f by auto
      have valcons:"valid ((x,T)#\<Gamma>')" using `valid \<Gamma>'` `x \<sharp> \<Gamma>'` by auto
      have "\<turnstile> Ta <: T" using `\<turnstile> Ta <: T0``\<turnstile> T0 <: T`  by auto

      hence "EX T2'. \<Gamma>' \<turnstile> b[x::=v] : T2' ; FF \<and> \<turnstile> T2' <: T1'" using X3 
	using subst_produces_FF[OF X4 `\<Gamma>' \<turnstile> v : Ta ; eff2` `\<turnstile> Ta <: T` valcons ` closed v`` v \<in> values` _] 
	by auto     
      thus ?case using `\<turnstile> T1' <: T'` by auto
    qed
    thus ?case .
  qed

lemma value_no_ctxt:
  assumes "v : values" and "v = E t" and "E : ctxt"
  shows "E = (% t . t)"
  using prems
  proof (induct)
    case bi_value show ?case using `E : ctxt` bi_value
      by (induct E rule: ctxt.induct) (auto simp add: trm.inject)
  next
    case num_value show ?case using `E : ctxt` num_value
      by (induct E rule: ctxt.induct) (auto simp add: trm.inject)
  next
    case abs_value show ?case using `E : ctxt` abs_value
      by (induct E rule: ctxt.induct) (auto simp add: trm.inject)
  next
    case bool_value show ?case using `E : ctxt` bool_value
      by (induct E rule: ctxt.induct) (auto simp add: trm.inject)
  qed


lemma subst_in_ctxt_preserves_type:
  assumes a:"\<Gamma> \<turnstile> u : T ; F"
  and b:"C : ctxt"
  and c:"u = C e"
  and "~ (e : values)"
  and "closed (C e)" and "closed (C e')"
  and "!! T0 F0  . \<Gamma> \<turnstile> e : T0 ; F0 \<Longrightarrow> EX T1 F1. \<Gamma> \<turnstile> e' : T1 ; F1 \<and> \<turnstile> T1 <: T0 \<and> \<turnstile> F1 <e: F0"
  shows "EX S G. \<Gamma> \<turnstile> C e' : S ; G \<and> \<turnstile> S <: T \<and> \<turnstile> G <e: F"
  using b prems
  proof (induct C arbitrary: u e e' T F rule: ctxt.induct)
    case C_Hole
    hence "\<Gamma> \<turnstile> e : T ; F" using C_Hole by simp
    hence "EX S G. \<Gamma> \<turnstile> e' : S; G \<and> \<turnstile> S <: T \<and> \<turnstile> G <e: F" using C_Hole by auto
    thus ?case by simp
  next
    case (C_App1 E arg u' t t' T' F')
    have A:"closed (E t)" and B:"closed (E t')" using C_App1 closed_def trm.supp by auto
    have C:"\<Gamma> \<turnstile> App (E t) arg : T' ; F'" using C_App1 by auto
    hence D:"simple_eff F'" using C_App1 closed_eff by auto
    thus ?case using C_App1 A B C
      proof (induct rule: simple_eff_cases)
        case NE
        hence "EX T0 T0' T1 le eff' eff'' U.  \<Gamma> \<turnstile> E t :U ; eff'  \<and>  \<Gamma> \<turnstile> arg : T0' ; eff''  \<and> \<turnstile> U <:  T0 \<rightarrow> T1 : le
	  \<and> \<turnstile> T0' <: T0 \<and> T1 = T'"
          using app_ty_elim by auto
        then obtain T0 T0' le eff' eff'' U
          where  a:"\<Gamma> \<turnstile> E t : U ; eff'" and b:"\<Gamma> \<turnstile> arg : T0' ; eff''" and c:"\<turnstile> T0' <: T0"  and d:"\<turnstile> U <: T0 \<rightarrow> T' : le"
	  by auto
        have  "\<exists>S G.  \<Gamma> \<turnstile> E t' : S ; G  \<and> \<turnstile> S <: U \<and> \<turnstile> G <e: eff'"
          using C_App1(2)[of "E t" _ eff' t t']  `E : ctxt` `closed (E t)` `closed (E t')` C_App1(8) a
	  `t \<notin> values` C_App1 by auto
        then obtain S G where et'ty:"\<Gamma> \<turnstile> E t' : S ; G " and subarr:" \<turnstile> S <: U " and "\<turnstile> G <e: eff'" by auto
	hence "\<Gamma> \<turnstile> App (E t') arg : T' ; NE" using b c d by auto
        thus ?case   by auto
      next
        case FF
        have "EX S T0 T0' le F1 F2 U.  \<Gamma> \<turnstile> E t : U ; F1  \<and>  \<Gamma> \<turnstile> arg : T0' ; F2 \<and> \<turnstile> T0' <: T0 \<and> le = Latent S \<and> 
	  ~ (\<turnstile> T0' <: S) \<and> arg : values \<and> closed arg \<and> \<turnstile> U <: T0 \<rightarrow> T' : le"
          using `\<Gamma> \<turnstile> App (E t) arg : T' ; FF` app_ty_ff_elim[of \<Gamma> "E t" arg T'] by blast
        then obtain S T0 T0' F1 F2 U where  a:"\<Gamma> \<turnstile> E t :U ; F1" and  b:"\<Gamma> \<turnstile> arg : T0' ; F2 " 
	  and c:"\<turnstile> T0' <: T0 " and d:" ~ (\<turnstile> T0' <: S)"  "closed arg" "arg : values" " \<turnstile> U <:  T0 \<rightarrow> T' : Latent S"
          by auto
        have  "\<exists>S' G.  \<Gamma> \<turnstile> E t' : S' ; G  \<and> \<turnstile> S' <: U \<and> \<turnstile> G <e: F1"
          using C_App1(2)[of "E t" U F1 t t']  `E : ctxt` `closed (E t)` `closed (E t')` C_App1(8) a C_App1 by auto
        then obtain S' G where et'ty:"\<Gamma> \<turnstile> E t' : S' ; G " and subarr:" \<turnstile> S' <: U" and "\<turnstile> G <e: F1" by auto
	hence "\<Gamma> \<turnstile> App (E t') arg : T' ; FF" using b c d by auto
        thus ?case by auto
      next
        case TT
        have "EX S T0 T0' le F1 F2 U.  \<Gamma> \<turnstile> E t : U ; F1  \<and>  \<Gamma> \<turnstile> arg : T0' ; F2 \<and> \<turnstile> T0' <: T0 \<and> 
	  le = Latent S \<and> \<turnstile> T0' <: S \<and>  \<turnstile> U <: T0 \<rightarrow> T' : le"
          using `\<Gamma> \<turnstile> App (E t) arg : T' ; TT` app_ty_tt_elim[of \<Gamma> "E t" arg T'] by blast
        then obtain S T0 T0' F1 F2 U where  a:"\<Gamma> \<turnstile> E t : U ; F1" and  b:"\<Gamma> \<turnstile> arg : T0' ; F2 " 
	  and c:"\<turnstile> T0' <: T0 " and d:"\<turnstile> T0' <: S" "\<turnstile> U <: T0 \<rightarrow> T' : Latent S"
          by auto
        have  "\<exists>S' G.  \<Gamma> \<turnstile> E t' : S' ; G  \<and> \<turnstile> S' <: U \<and> \<turnstile> G <e: F1"
          using C_App1(2)[of "E t" U F1 t t']  `E : ctxt` `closed (E t)` `closed (E t')` C_App1 a by auto
        then obtain S' G where et'ty:"\<Gamma> \<turnstile> E t' : S' ; G " and subarr:" \<turnstile> S' <: U " and "\<turnstile> G <e: F1" by auto
	hence "\<Gamma> \<turnstile> App (E t') arg : T' ; TT" using b c d by auto
        thus ?case by auto
      qed
    next
      case (C_App2 E v u' t t' T' F')
      have A:"closed (E t)" and B:"closed (E t')" using C_App2 closed_def trm.supp by auto
      have C:"\<Gamma> \<turnstile> App v (E t) : T' ; F'" using C_App2 by auto
      hence D:"simple_eff F'" using C_App2 closed_eff by auto
      thus ?case using C_App2 A B C
      proof (induct rule: simple_eff_cases)
        case NE
	have "\<exists>T0 T0' T1 le eff' eff'' U.  \<Gamma> \<turnstile> v : U ; eff'  \<and>  \<Gamma> \<turnstile> E t : T0' ; eff''  \<and> \<turnstile> T0' <: T0 
	  \<and> T1 = T' \<and> \<turnstile> U <: T0 \<rightarrow> T1 : le"
	  using  app_ty_elim[of \<Gamma> v "E t" T' F'] `\<Gamma> \<turnstile> App v (E t) : T' ; F'` by blast
	then obtain T0 T0' le eff' eff'' U
	  where  a:"\<Gamma> \<turnstile> v : U ; eff'"  " \<Gamma> \<turnstile> E t : T0' ; eff'' " "\<turnstile> T0' <: T0" "\<turnstile> U <: T0 \<rightarrow> T' : le" by auto
	hence "\<exists>S G.  \<Gamma> \<turnstile> E t' : S ; G  \<and> \<turnstile> S <: T0' \<and> \<turnstile> G <e: eff''" using NE(2)[of "E t" T0' eff'' t t'] NE by auto
	then obtain S G where  "\<Gamma> \<turnstile> E t' : S ; G "" \<turnstile> S <: T0'" by auto
	hence "\<Gamma> \<turnstile> App v (E t') : T' ; eff.NE" using a `\<turnstile> T0' <: T0` by auto
	thus ?case by auto
      next
        case FF 
	have "\<exists>S T0 T0' le eff' eff'' U.  \<Gamma> \<turnstile> v : U ; eff'  \<and>  \<Gamma> \<turnstile> E t : T0' ; eff''  \<and> \<turnstile> T0' <: T0  \<and> le = Latent S \<and> ~ (\<turnstile> T0' <: S) \<and> E t : values \<and> closed (E t) \<and> \<turnstile> U <:  T0 \<rightarrow> T' : le"	  
	  using  app_ty_ff_elim[of \<Gamma> v "E t" T'] `\<Gamma> \<turnstile> App v (E t) : T' ; FF` by blast
	then obtain S T0 T0' le eff' eff'' U 
	  where "\<Gamma> \<turnstile> v : U ; eff'  "" \<Gamma> \<turnstile> E t : T0' ; eff''  "" \<turnstile> T0' <: T0 " " ~ (\<turnstile> T0' <: S) "
	  " E t : values "" closed (E t)"
	  by auto
	hence "E = (% t. t)" using  value_no_ctxt[of "E t" E t] `E : ctxt` by simp
	hence "t : values" using `E t : values` by simp
	thus ?case using `t \<notin> values` by auto
      next
        case TT
	have "\<exists>S T0 T0' le eff' eff'' U.  \<Gamma> \<turnstile> v : U ; eff'  \<and>  \<Gamma> \<turnstile> E t : T0' ; eff''  \<and> \<turnstile> T0' <: T0  \<and> 
	  le = Latent S \<and> \<turnstile> T0' <: S \<and> \<turnstile> U <: T0 \<rightarrow> T' : le"
	  using  app_ty_tt_elim[of \<Gamma> v "E t" T'] `\<Gamma> \<turnstile> App v (E t) : T' ; TT` by blast
	then obtain S T0 T0' le eff' eff'' U
	  where a:"\<Gamma> \<turnstile> v : U ; eff'  "" \<Gamma> \<turnstile> E t : T0' ; eff''  "" \<turnstile> T0' <: T0 " " \<turnstile> T0' <: S" "\<turnstile> U <: T0 \<rightarrow> T' : Latent S"
	  by auto
	hence "\<exists>S' G.  \<Gamma> \<turnstile> E t' : S' ; G  \<and> \<turnstile> S' <: T0' \<and> \<turnstile> G <e: eff''" using TT(2)[of "E t" T0' eff'' t t'] TT by auto
	then obtain S' G where  b:"\<Gamma> \<turnstile> E t' : S' ; G "" \<turnstile> S' <: T0'" by auto
	have "\<turnstile> S' <: S" using ` \<turnstile> S' <: T0'` `\<turnstile> T0' <: S` by auto
	have "\<turnstile> S' <: T0" using `\<turnstile> S' <: T0'` `\<turnstile> T0' <: T0` by auto
	hence "\<Gamma> \<turnstile> App v (E t') : T' ; TT" using b T_AppPredTrue[OF a(1) a(5) b(1) `\<turnstile> S' <: T0` ] using `\<turnstile> S' <: S` by auto
	thus ?case by auto
      qed
    next
      case (C_Iff E thn els u' t t' T' F')
      have A:"closed (E t)" and B:"closed (E t')" using C_Iff closed_def trm.supp by auto
      have C:"\<Gamma> \<turnstile> Iff (E t) thn els: T' ; F'" using C_Iff by auto
      hence
	bigor:
	"(\<exists>T1 T2 T3 F1 F2 F3. \<Gamma> \<turnstile> E t : T1 ; F1  \<and> \<Gamma> |+ F1 \<turnstile> thn : T2 ; F2  \<and>  \<Gamma> |- F1 \<turnstile> els : T3 ; F3  \<and> \<turnstile> T2 <: T' \<and> \<turnstile> T3 <: T' \<and> F' = eff.NE) \<or>
	(\<exists>T1 T3 F3.  \<Gamma> \<turnstile> E t : T1 ; FF  \<and>  \<Gamma> \<turnstile> els : T3 ; F3  \<and> \<turnstile> T3 <: T' \<and> F' = eff.NE) \<or>
	(\<exists>T1 T2 F2.  \<Gamma> \<turnstile> E t : T1 ; TT  \<and>  \<Gamma> \<turnstile> thn : T2 ; F2  \<and> \<turnstile> T2 <: T' \<and> F' = eff.NE)"
	using if_ty_elim[of \<Gamma> "(E t)" thn els T' F'] by auto
      thus ?case
	proof -
	  {
	    assume "(\<exists>T1 T2 T3 F1 F2 F3. \<Gamma> \<turnstile> E t : T1 ; F1  \<and> \<Gamma> |+ F1 \<turnstile> thn : T2 ; F2  \<and>  \<Gamma> |- F1 \<turnstile> els : T3 ; F3  \<and> \<turnstile> T2 <: T' \<and> \<turnstile> T3 <: T' \<and> F' = eff.NE)"
	    then obtain T1 T2 T3 F1 F2 F3 where 
	      P:"\<Gamma> \<turnstile> E t : T1 ; F1""\<Gamma> |+ F1 \<turnstile> thn : T2 ; F2""\<Gamma> |- F1 \<turnstile> els : T3 ; F3""\<turnstile> T2 <: T'""\<turnstile> T3 <: T'""F' = eff.NE"
	      by auto
	    have "closed (E t)" and "closed (E t')" using prems trm.supp closed_def by auto
	    hence "EX T1' F1'. \<Gamma> \<turnstile> E t' : T1' ; F1' \<and> \<turnstile> T1' <: T1 \<and> \<turnstile> F1' <e: F1"
	      using C_Iff(2)[of "E t" T1 F1 t t'] C_Iff P by auto
	    then obtain T1' F1' where Q:"\<Gamma> \<turnstile> E t' : T1' ; F1' "" \<turnstile> T1' <: T1 "" \<turnstile> F1' <e: F1" by auto
	    have "simple_eff F1'" and "simple_eff F1" using `closed (E t)` `closed (E t')` P Q closed_eff by auto
	    hence "\<Gamma> |+ F1 = \<Gamma>" "\<Gamma> |- F1 = \<Gamma>" "\<Gamma> |+ F1' = \<Gamma>" "\<Gamma> |- F1' = \<Gamma>" by (auto simp add: env_plus_simple_eff)
	    hence "\<Gamma> |+ F1' \<turnstile> thn : T2 ; F2 " "\<Gamma> |- F1' \<turnstile> els : T3 ; F3" using P by auto
	    hence "\<Gamma> \<turnstile> Iff (E t') thn els : T'; comb_eff F1' F2 F3" using `\<Gamma> \<turnstile> E t' : T1' ; F1'` ` \<turnstile> T2 <: T' `` \<turnstile> T3 <: T'`
	      by (auto simp del: comb_eff.simps)
	    hence ?thesis using `F' = NE` by auto
	  }
	  moreover
	  {
	    assume "(\<exists>T1 T3 F3.  \<Gamma> \<turnstile> E t : T1 ; FF  \<and>  \<Gamma> \<turnstile> els : T3 ; F3  \<and> \<turnstile> T3 <: T' \<and> F' = eff.NE)"
	    then obtain T1 T3 F3 where P:"\<Gamma> \<turnstile> E t : T1 ; FF "" \<Gamma> \<turnstile> els : T3 ; F3  "" \<turnstile> T3 <: T'"" F' = eff.NE"
	      by auto
	    have "closed (E t)" and "closed (E t')" using prems trm.supp closed_def by auto
	    hence "EX T1' F1'. \<Gamma> \<turnstile> E t' : T1' ; F1' \<and> \<turnstile> T1' <: T1 \<and> \<turnstile> F1' <e: FF"
	      using C_Iff(2)[of "E t" T1 FF t t'] C_Iff P by auto
	    then obtain T1' F1' where Q:"\<Gamma> \<turnstile> E t' : T1' ; F1' "" \<turnstile> T1' <: T1 "" \<turnstile> F1' <e: FF" by auto
	    have "F1' = FF" using Q no_sub_FF[of F1' FF] by simp
	    hence "\<Gamma> \<turnstile> E t' : T1' ; FF " using Q by auto
	    hence ?thesis using P by auto
	  }
	  moreover
	  {
	    assume "(\<exists>T1 T2 F2.  \<Gamma> \<turnstile> E t : T1 ; TT  \<and>  \<Gamma> \<turnstile> thn : T2 ; F2  \<and> \<turnstile> T2 <: T' \<and> F' = eff.NE)"
	    then obtain T1 T2 F2 where P:"\<Gamma> \<turnstile> E t : T1 ; TT "" \<Gamma> \<turnstile> thn : T2 ; F2  "" \<turnstile> T2 <: T'"" F' = eff.NE"
	      by auto
	    have "closed (E t)" and "closed (E t')" using prems trm.supp closed_def by auto
	    hence "EX T1' F1'. \<Gamma> \<turnstile> E t' : T1' ; F1' \<and> \<turnstile> T1' <: T1 \<and> \<turnstile> F1' <e: TT"
	      using C_Iff(2)[of "E t" T1 TT t t'] C_Iff P by auto
	    then obtain T1' F1' where Q:"\<Gamma> \<turnstile> E t' : T1' ; F1' "" \<turnstile> T1' <: T1 "" \<turnstile> F1' <e: TT" by auto
	    have "F1' = TT" using Q no_sub_TT[of F1' TT] by simp
	    hence "\<Gamma> \<turnstile> E t' : T1' ; TT " using Q by auto
	    hence ?thesis using P by auto
	  }
	  ultimately show ?thesis using bigor by blast
	qed
      qed        
        

lemma typing_ctxt:
  assumes a:"\<Gamma> \<turnstile> C L : T ; eff"
  and b:"C : ctxt"
  shows "EX T' eff'. \<Gamma> \<turnstile> L : T' ; eff'"
  using b a
  proof(induct C arbitrary: T eff rule: ctxt.induct )
    case C_Hole thus ?case by auto
  next
    case (C_App1 C' arg S)
    hence ih: "!! T0 eff. \<Gamma> \<turnstile> C' L : T0 ; eff  \<Longrightarrow> \<exists>T' a.  \<Gamma> \<turnstile> L : T' ; a" by simp
    obtain T0 T0' T1 le eff' eff'' U where "\<Gamma> \<turnstile> C' L : U ; eff'" "\<Gamma> \<turnstile> arg : T0' ; eff''" "\<turnstile> T0' <: T0 \<and> T1 = S"    
      "\<turnstile> U <:  T0 \<rightarrow> T1 : le"
      using app_ty_elim[of \<Gamma> "C' L" arg S eff] ` \<Gamma> \<turnstile> App (C' L) arg : S ; eff` by blast
    thus ?case using ih by auto
  next
    case (C_App2 C' rator S F)
    hence ih: "!! T0 eff. \<Gamma> \<turnstile> C' L : T0 ; eff  \<Longrightarrow> \<exists>T' a.  \<Gamma> \<turnstile> L : T' ; a" by simp
    obtain T0 T0' T1 le eff' eff'' U where "\<Gamma> \<turnstile> rator : U ; eff'" "\<Gamma> \<turnstile> C' L : T0' ; eff''" "\<turnstile> T0' <: T0 \<and> T1 = S"  
      "\<turnstile> U <: T0 \<rightarrow> T1 : le"
      using app_ty_elim[of \<Gamma> rator "C' L" S F] ` \<Gamma> \<turnstile> App rator (C' L)  : S ; F` by blast
    thus ?case using ih by auto
  next
    case (C_Iff C' thn els S F)
    hence ih: "!! T0 eff. \<Gamma> \<turnstile> C' L : T0 ; eff  \<Longrightarrow> \<exists>T' a.  \<Gamma> \<turnstile> L : T' ; a" by simp
    obtain T0 eff' where  "\<Gamma> \<turnstile> C' L : T0 ; eff'"
      using if_ty_elim[of \<Gamma> "C' L" thn els S F] ` \<Gamma> \<turnstile> Iff (C' L) thn els : S ; F` by auto
    thus ?case using ih by auto
  qed

inductive_cases step_cases: "(e::trm) \<longrightarrow> e'"


inductive_cases bi_reduce:"BI b \<hookrightarrow> x"
inductive_cases bool_reduce:"Bool b \<hookrightarrow> x"
inductive_cases abs_reduce:"(Lam[a:T].b) \<hookrightarrow> x"
inductive_cases num_reduce:"Num n \<hookrightarrow> x"

lemma value_reduce_step:
  assumes A:"v : values" and B:"v \<longrightarrow> (v'::trm)"
  shows "v \<hookrightarrow> v'"
  using B A
  proof(induct)
    fix E L R
    assume "E : ctxt" "L \<hookrightarrow> R" "E L \<in> values"
    hence "E L = L" and "E R = R" using value_no_ctxt by auto
    thus "E L \<hookrightarrow> E R" using prems by auto
  qed

lemma value_not_step:
  assumes "v : values"
  shows "~ (EX v'. v \<hookrightarrow> v')"
proof(rule ccontr, simp)
  assume "\<exists>v'. v \<hookrightarrow> v'"
  then obtain v' where A:"v \<hookrightarrow> v'" by auto
  show False using `v : values` A
    proof (induct v rule: values.induct)
      case (bi_value b) thus ?case using bi_reduce by auto
    next
      case num_value thus ?case using num_reduce by auto
    next
      case abs_value thus ?case using abs_reduce by blast
    next
      case bool_value thus ?case using bool_reduce by auto
    qed
  qed


lemma value_not_reduce:
  fixes v v' :: trm
  assumes "v : values"
  shows "~ (EX v'. v \<longrightarrow> v')"
proof (rule ccontr)
  assume "\<not> \<not> (\<exists>v'.  v \<longrightarrow> v')"
  then obtain v' where "v \<longrightarrow> v'" by auto
  hence A:"v \<hookrightarrow> v'" using value_reduce_step prems by auto
  show False using `v : values` A value_not_step by auto
qed


theorem preservation:
  fixes e e' :: trm
  assumes typed:"\<Gamma> \<turnstile> e : t ; eff" and cl:"closed e"
  and red:"e \<longrightarrow> e'"
  shows "EX t' eff'. \<Gamma> \<turnstile> e' : t' ; eff' \<and> \<turnstile> t' <: t \<and> \<turnstile> eff' <e: eff"
  using red typed cl
proof -
  have val:"valid \<Gamma>" using typing_valid typed by auto
  obtain C L R where "e = C L" "e' = C R" and "L \<hookrightarrow> R" and "C : ctxt" using red step_cases[of e e' thesis] by auto
  hence f:"EX T F. \<Gamma> \<turnstile> L : T ; F" using typed typing_ctxt by auto
  have "L \<notin> values" using `L \<hookrightarrow> R` value_not_step by auto
  have "closed L" and "closed_ctxt C" using closed_in_ctxt_closed_ctxt[of e C L] `C : ctxt`  cl `e = C L` by auto
  hence "closed R" using reduce_closed[of L R] `L  \<hookrightarrow> R` by auto
  hence "closed (C R)" and "closed (C L)"  using `closed_ctxt C` ctxt_closed[of C L] ctxt_closed[of C R] `closed L` by auto
  have " \<And>T0 F0. \<Gamma> \<turnstile> L : T0 ; F0  \<Longrightarrow> \<exists>T1 F1.  \<Gamma> \<turnstile> R : T1 ; F1  \<and> \<turnstile> T1 <: T0 \<and> \<turnstile> F1 <e: F0"
  proof -
    fix T0 F0
    show "\<Gamma> \<turnstile> L : T0 ; F0 \<Longrightarrow>  (\<exists>T1 F1.  \<Gamma> \<turnstile> R : T1 ; F1  \<and> \<turnstile> T1 <: T0 \<and> \<turnstile> F1 <e: F0)"
      using `e = C L` `C : ctxt` `L \<hookrightarrow> R` closed_in_ctxt[of C L] cl preserve_red[of \<Gamma> L T0 F0 R] `closed L` val by auto
  qed
  hence "\<exists>S G.  \<Gamma> \<turnstile> C R : S ; G  \<and> \<turnstile> S <: t \<and> \<turnstile> G <e: eff"
    using `C : ctxt` subst_in_ctxt_preserves_type[of \<Gamma> e t eff C L R] typed `e = C L` `closed (C L)` `closed (C R)`
      `L \<notin> values`by auto
  thus ?thesis using `e' = C R` by auto
qed

text {* soundness *}

lemma soundness_finite:
  fixes e e' e'' :: trm
  assumes A:"\<Gamma> \<turnstile> e : T ; F" and B:"e \<longrightarrow>\<^sup>* e'" and C:"~ (EX e''. e' \<longrightarrow> e'')" and E:"closed e"
  shows "EX T' F'. (e' : values \<and> \<Gamma> \<turnstile> e' : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F)"
  using B prems
proof (induct arbitrary: \<Gamma> T F rule: step_multi.induct)
  case (sm_refl v)
  have "v : values" using sm_refl progress[of \<Gamma> v T F] by auto
  thus ?case using sm_refl by auto
next
  case (sm_trans a b c)
  have "closed b" "closed c" using `closed a` `b \<longrightarrow>\<^sup>* c` `a \<longrightarrow> b` step_closed[of a b] multi_step_closed[of b c] by auto
  then obtain T' F' where 1:"\<Gamma> \<turnstile> b : T' ; F'"  "\<turnstile> T' <: T" "\<turnstile> F' <e: F"
    using preservation[of \<Gamma> a T F b] sm_trans by auto
  then obtain T'' F'' where 2:"\<Gamma> \<turnstile> c : T'' ; F''"  "\<turnstile> T'' <: T'"  "\<turnstile> F'' <e: F'" "c : values"
    using  sm_trans(3)[of \<Gamma> T' F'] sm_trans `closed b` by blast
  have "\<turnstile> T'' <: T" using 1 2 by auto
  have 3:"simple_eff F" using prems closed_eff by auto
  have 4:"simple_eff F'" using 1 prems closed_eff `closed b` by auto
  have 5:"simple_eff F''" using  prems closed_eff `closed c` by auto
  from 3 4 5 have "\<turnstile> F'' <e: F" using SE_Trans[of F'' F' F] 1 2 by auto
  thus ?case using 2 `\<turnstile> T'' <: T`  by auto
qed

text
{*
    interesting fact:
    let e = (Iff True 3 x)
    then [] \<turnstile> e : Int ; NE
    but e is not closed
*}


theorem soundness:
  assumes A:"\<Gamma> \<turnstile> e : T ; F" and E:"closed e" 
  shows "reduce_forever e \<or> (EX v T' F'. (v : values \<and> e \<longrightarrow>\<^sup>* v \<and> \<Gamma> \<turnstile> v : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F))"
proof -
  {
    assume "~(reduce_forever e)"
    hence "EX e'. (e \<longrightarrow>\<^sup>* e') \<and> ~(EX e''. e' \<longrightarrow> e'')" by (auto simp add: reduce_forever_def)
    then obtain e'::trm where B:"e \<longrightarrow>\<^sup>* e'" and C:"~ (EX e''. e' \<longrightarrow> e'')" by auto
    hence ?thesis using soundness_finite[OF A B C E] by auto
  }
  moreover
  {
    assume "reduce_forever e" 
    hence ?thesis by simp
  }
  ultimately show ?thesis by auto
qed

text {* simpler type system, without silly rules *}

inductive
  typing2 :: "varEnv \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> eff \<Rightarrow> bool" (" _ \<turnstile>\<^isub>2 _ : _ ; _ " [60,60,60,60] 60) 
where
  T2_Var[intro]:   "\<lbrakk>valid \<Gamma>; (v,T)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile>\<^isub>2 Var v : T ; VE v" 
| T2_Const[intro]: "valid \<Gamma> \<Longrightarrow> \<Delta>\<^isub>\<tau> b = T \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>2 (BI b) : T ; TT"
| T2_Num[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>2 (Num n) : ty.Int ; TT"
| T2_True[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>2 (Bool True) : ty.TT ; TT"
| T2_False[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>2 (Bool False) : ty.FF ; FF"
| T2_Abs[intro]:   "\<lbrakk>x \<sharp> \<Gamma>; ((x,T1)#\<Gamma>) \<turnstile>\<^isub>2 b : T2; eff\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>2 Lam [x:T1].b : (T1\<rightarrow>T2 : latent_eff.NE) ; TT"
| T2_App[intro]: "\<lbrakk>\<Gamma> \<turnstile>\<^isub>2 e1 : U ; eff1 ; \<turnstile> U <: (T0 \<rightarrow> T1 : le); \<Gamma> \<turnstile>\<^isub>2 e2 : T; eff2 ;  \<turnstile> T <: T0\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>2 App e1 e2 : T1 ; NE"
| T2_AppPred[intro]: "\<lbrakk>\<Gamma> \<turnstile>\<^isub>2 e1 : U; eff1; \<turnstile> U <: (T0 \<rightarrow> T1 : Latent S);  \<Gamma> \<turnstile>\<^isub>2 e2 : T; VE x ;  \<turnstile> T <: T0\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>2 App e1 e2 : T1 ; TE S x"
| T2_If[intro]: "\<lbrakk>\<Gamma> \<turnstile>\<^isub>2 e1 : T1; eff1; (\<Gamma> |+ eff1) \<turnstile>\<^isub>2 e2 : T2; eff2; (\<Gamma> |- eff1) \<turnstile>\<^isub>2 e3 : T3; eff3; \<turnstile> T2 <: T; \<turnstile> T3 <: T\<rbrakk> \<Longrightarrow>
  \<Gamma> \<turnstile>\<^isub>2 (Iff e1 e2 e3) : T ; comb_eff eff1 eff2 eff3"
| T2_AbsPred[intro]:   "\<lbrakk>x \<sharp> \<Gamma>; ((x,T1)#\<Gamma>) \<turnstile>\<^isub>2  b : T2; TE S x\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>2 Lam [x:T1].b : (T1\<rightarrow>T2 : Latent S) ; TT"

lemma typing2_typing:
  assumes "\<Gamma> \<turnstile>\<^isub>2 e : T ; F"
  shows "\<Gamma> \<turnstile> e : T ; F"
  using prems
  by induct (auto simp del: comb_eff.simps)

lemma typing2_soundness1:
  assumes A:"\<Gamma> \<turnstile>\<^isub>2 e : T ; F" and E:"closed e" 
  shows "reduce_forever e \<or> (EX v T' F'. (v : values \<and> e \<longrightarrow>\<^sup>* v \<and> \<Gamma> \<turnstile> v : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F))"
  using A E soundness typing2_typing
  by auto

lemma typing2_soundness_int:
  assumes A:"\<Gamma> \<turnstile>\<^isub>2 e : ty.Int ; F" and E:"closed e" 
  shows "reduce_forever e \<or> (EX v F'. (v : values \<and> (e  \<longrightarrow>\<^sup>* v) \<and> \<Gamma> \<turnstile>\<^isub>2 v : ty.Int ; F' \<and> \<turnstile> F' <e: F))"
proof -
  from typing2_soundness1[OF A E]
  have B:"reduce_forever e \<or> (EX v T' F'. (v : values  \<and> (e  \<longrightarrow>\<^sup>* v) \<and> \<Gamma> \<turnstile> v : T' ; F' \<and> \<turnstile> T' <: ty.Int \<and> \<turnstile> F' <e: F))" by auto
  thus ?thesis
  proof 
    assume "EX v T' F'. (v : values  \<and> (e  \<longrightarrow>\<^sup>* v) \<and> \<Gamma> \<turnstile> v : T' ; F' \<and> \<turnstile> T' <: ty.Int \<and> \<turnstile> F' <e: F)"
    then guess v T' F' by auto
    then obtain n where "v = Num n" using int_value by blast
    hence "\<Gamma> \<turnstile>\<^isub>2 v : ty.Int ; F'" using num_ty_elim[of \<Gamma> _ T' F'] `\<Gamma> \<turnstile> v : T' ; F'` by auto
    thus ?thesis  using `\<turnstile> F' <e: F` `v : values` `(e  \<longrightarrow>\<^sup>* v)` by auto
  qed (auto)
qed

lemma typing2_soundness_help:
  assumes A:"\<Gamma> \<turnstile>\<^isub>2 e : \<sigma> ; F" and E:"closed e" 
  and B: "((\<exists>v T' F'. v \<in> values \<and>  \<Gamma> \<turnstile> v : T' ; F'  \<and> \<turnstile> T' <: \<sigma> \<and> \<turnstile> F' <e: F)) \<Longrightarrow>  
  (reduce_forever e \<or> (\<exists>v F'. v \<in> values \<and>  \<Gamma> \<turnstile>\<^isub>2 v : \<sigma> ; F'  \<and> \<turnstile> F' <e: F))"
  shows "(reduce_forever e \<or> (\<exists>v F'. v \<in> values \<and>  \<Gamma> \<turnstile>\<^isub>2 v : \<sigma> ; F'  \<and> \<turnstile> F' <e: F))"
  using A B E typing2_soundness1 by blast

lemma typing2_soundness_bool:
  assumes A:"\<Gamma> \<turnstile>\<^isub>2 e : T ; F" and E:"closed e" and sub:"\<turnstile> T <: BoolTy"
  shows "reduce_forever e \<or> (EX v F' T'. (v : values \<and> (e  \<longrightarrow>\<^sup>* v) \<and> \<Gamma> \<turnstile>\<^isub>2 v : T' ; F' \<and> \<turnstile> F' <e: F \<and> \<turnstile> T' <: T))"
proof -
  from typing2_soundness1[OF A E]
  have B:"reduce_forever e \<or> (EX v T' F'. (v : values \<and> (e  \<longrightarrow>\<^sup>* v) \<and> \<Gamma> \<turnstile> v : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F))"
    by blast
  thus ?thesis
  proof
    assume "EX v T' F'. (v : values \<and> (e  \<longrightarrow>\<^sup>* v) \<and> \<Gamma> \<turnstile> v : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F)"
    then guess v T' F' by auto
    then obtain b where "v = Bool b" using bool_value[OF `v : values` `\<Gamma> \<turnstile> v : T' ; F'`] sub by auto
    hence "\<Gamma> \<turnstile>\<^isub>2 Bool b : T' ; F'" using `\<Gamma> \<turnstile> v : T' ; F'`
      true_ty_elim[of \<Gamma> T' F'] false_ty_elim[of \<Gamma> T' F']
      by (cases b) auto
    thus ?thesis using `v = Bool b`  `e  \<longrightarrow>\<^sup>* v` `v : values` `\<turnstile> F' <e: F` `\<turnstile> T' <: T` by blast
  qed (auto)
qed

constdefs
  ground_type :: "ty \<Rightarrow> bool"
  "ground_type t == t = ty.Int \<or> t = BoolTy \<or> t = ty.TT \<or> t = ty.FF"


lemma supp_env:
  "(a,b) : set (\<Gamma> :: varEnv) \<Longrightarrow> a : supp \<Gamma>"
  by (induct \<Gamma>) (auto simp add: supp_list_cons supp_prod supp_atm)

lemma envop_supp:
  assumes "valid \<Gamma>"
  shows "x : (supp (envop f n t \<Gamma>)) \<Longrightarrow> x : (supp \<Gamma> :: name set)"
proof -
  assume A:"x : (supp (envop f n t \<Gamma>))"
  have "!! a. a \<notin> (supp \<Gamma> :: name set) \<Longrightarrow> a \<notin> supp (envop f n t \<Gamma>)"
  proof -
    fix a
    show  "a \<notin> (supp \<Gamma> :: name set) \<Longrightarrow> a \<notin> supp (envop f n t \<Gamma>)"
      using fresh_def[of a "envop f n t \<Gamma>"] envop_fresh[OF _  `valid \<Gamma>`] fresh_def[of a \<Gamma>]
      by auto
  qed
  hence "(supp (envop f n t \<Gamma>)) <= (supp \<Gamma> :: name set)" by blast
  thus ?thesis using A by auto
qed

declare envop_def[simp del]

lemma envplus_supp:
  assumes "valid \<Gamma>"
  shows "(supp (\<Gamma> |+ F) :: name set) <= (supp \<Gamma> :: name set)"
  using prems
  apply (nominal_induct F rule: eff.induct)
  apply (auto simp add: envop_supp)
  done

lemma envminus_supp:
  assumes "valid \<Gamma>"
  shows "(supp (\<Gamma> |- F) :: name set) <= (supp \<Gamma> :: name set)"
  using prems
  apply (nominal_induct F rule: eff.induct)
  apply (auto simp add: envop_supp)
  done

lemma env_supp_typing2:
  assumes "\<Gamma> \<turnstile>\<^isub>2 e : T ; F"
  shows "fv e <= supp \<Gamma>"
  using prems
proof (induct \<Gamma> e T F rule: typing2.induct)
  case T2_Var
  thus ?case by (auto simp add: trm.supp supp_atm supp_env)
next
  case T2_App thus ?case by (auto simp add: trm.supp)
next
  case T2_AppPred thus ?case by (auto simp add: trm.supp)
next
  case (T2_If \<Gamma> _ _ F)
  have "valid \<Gamma>" using typing_valid typing2_typing[OF T2_If(1)] by auto
  thus ?case using T2_If envminus_supp[OF `valid \<Gamma>`, of F] envplus_supp[OF `valid \<Gamma>`, of F]
    by (auto simp add: trm.supp)
next
  case T2_Abs thus ?case 
    by (auto simp add: trm.supp fv_lam abs_supp supp_list_cons supp_prod supp_latent_eff_ty supp_atm)
next
  case T2_AbsPred thus ?case 
    by (auto simp add: trm.supp fv_lam abs_supp supp_list_cons supp_prod supp_latent_eff_ty supp_atm)
next
  case (T2_Const \<Gamma> b) thus ?case
    by (nominal_induct b rule: builtin.induct)
     (auto simp add: trm.supp  builtin.supp)
qed (auto simp add: trm.supp supp_nat supp_bool)

lemma empty_env_typing2_closed:
  assumes "[] \<turnstile>\<^isub>2 e : T ; F"
  shows "closed e"
  using env_supp_typing2[OF prems] closed_def prems supp_list_nil
  by auto

theorem ground_type_soundness:
  assumes A:"[] \<turnstile>\<^isub>2 e : T ; F" and B:"ground_type T"
  shows "reduce_forever e \<or> (EX v T' F'. (v : values \<and> (e  \<longrightarrow>\<^sup>* v) \<and> [] \<turnstile>\<^isub>2 v : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F))"
proof -
  have E:"closed e" using empty_env_typing2_closed[OF A] by simp
  {
    assume "T = ty.Int"
    hence "reduce_forever e \<or> (EX v F'. (v : values \<and> (e  \<longrightarrow>\<^sup>* v) \<and> [] \<turnstile>\<^isub>2 v : ty.Int ; F' \<and> \<turnstile> F' <e: F))"
      using A E typing2_soundness_int by auto
    hence ?thesis using prems by auto
  }
  moreover
  {
    assume "T ~= ty.Int"
    hence "\<turnstile> T <: BoolTy" using B by (auto simp add: ground_type_def)
    hence "reduce_forever e \<or> (EX v F' T'. (v : values \<and> (e  \<longrightarrow>\<^sup>* v) \<and> [] \<turnstile>\<^isub>2 v : T' ; F' \<and> \<turnstile> F' <e: F \<and> \<turnstile> T' <: T))"
      using typing2_soundness_bool[OF A E] by auto
    hence ?thesis using prems by auto
  }
  ultimately show ?thesis using B ground_type_def by auto
qed


end


lemma unique_decomposition: 
  assumes a:"closed e"
  shows "\<lbrakk>E : ctxt; E t = e; E' : ctxt; E' t' = e\<rbrakk> \<Longrightarrow> E = E'"
  using a
  proof (nominal_induct e rule: trm.induct)
    case (Var v)
    have f1:"E = (%t. t)" using Var by cases auto
    have f2:"E'= (%t. t)" using `E' : ctxt` Var by cases auto
    from f1 f2 show ?case by simp
  next
    case (Bool c)
    have f1:"E = (%t. t)" using Bool by cases auto
    have f2:"E'= (%t. t)" using `E' : ctxt` Bool by cases auto
    from f1 f2 show ?case by simp
  next
    case (Num c)
    have f1:"E = (%t. t)" using Num by cases auto
    have f2:"E'= (%t. t)" using `E' : ctxt` Num by cases auto
    from f1 f2 show ?case by simp
  next
    case Abs
    have f1:"E = (%t. t)" using `E : ctxt` Abs by cases auto
    have f2:"E'= (%t. t)" using `E' : ctxt` Abs by cases auto
    from f1 f2 show ?case by simp
  next
    case (Iff tst thn els)
    {
      assume "tst \<notin> values"
      hence "EX E L R. tst = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R" using decomposition 
      have f1:"E = (%t. t)" using `E : ctxt` Iff apply cases apply (auto  simp add: trm.inject)
      have f2:"E'= (%t. t)" using `E' : ctxt` Iff by cases auto
      from f1 f2 have ?case by simp
      {
    oops
    
lemma fresh_fact: 
  fixes a::"name"
  assumes a: "a\<sharp>t1"
  and     b: "a\<sharp>t2"
  shows "a\<sharp>(t1[b::=t2])"
using a b
by (nominal_induct t1 avoiding: a b t2 rule: trm.induct)
   (auto simp add: abs_fresh fresh_atm)

lemma id_subs: "t[x::=Var x] = t"
by (nominal_induct t avoiding: x rule: trm.induct)
   (simp_all add: fresh_atm)

lemma random_eqvt[simp]:
  fixes pi :: "name prm"
shows "\<forall>T. T \<in> set Ts \<longrightarrow> \<turnstile> T <: S \<and> \<turnstile> pi \<bullet> T <: pi \<bullet> S \<Longrightarrow>
    \<forall>T. T \<in> set (pi \<bullet> Ts) \<longrightarrow> \<turnstile> T <: pi \<bullet> S"
proof - 
  assume 0:"\<forall>T. T \<in> set Ts \<longrightarrow> \<turnstile> T <: S \<and> \<turnstile> pi \<bullet> T <: pi \<bullet> S"
  hence 1:"!! T. T \<in> set Ts \<Longrightarrow> \<turnstile> T <: S \<and> \<turnstile> pi \<bullet> T <: pi \<bullet> S" by auto
  have A:"(pi \<bullet> Ts) = Ts" by (induct Ts) auto
  have B:"pi \<bullet> S = S" by auto
  have "!! T.  T \<in> set (pi \<bullet> Ts) \<Longrightarrow> \<turnstile> T <: pi \<bullet> S"
  proof -
    fix T
    assume "T \<in> set (pi \<bullet> Ts)"
    hence "T : set Ts" using A by auto
    hence "\<turnstile> T <: S" using 1 by auto
    thus "\<turnstile> T <: pi \<bullet> S" using B by auto
  qed
  thus ?thesis by auto
qed


text {* complete induction on typing derivations *}

lemma typing_induct_complete[consumes 1, case_names T_Var T_Const T_Num T_True T_False T_App T_Lam T_AppPred T_If 
  T_AppPredTrue T_AppPredFalse T_IfTrue T_IfFalse]:
  fixes  P :: "'a::fs_name\<Rightarrow>(name\<times>ty) list \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> eff \<Rightarrow> bool"
  and    \<Gamma> :: "(name\<times>ty) list"
  and    t :: "trm"
  and    T :: "ty"
  and    F :: "eff"
  and    x :: "'a::fs_name"
  assumes a: "\<Gamma> \<turnstile> t : T ; F"
  and a1:    "\<And>\<Gamma> (a::name) \<tau> x. valid \<Gamma> \<Longrightarrow> (a,\<tau>) \<in> set \<Gamma> \<Longrightarrow> 
  (!! x t T \<Gamma> F. (t\<guillemotleft>Var a) \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> P x \<Gamma> (Var a) \<tau> (VE a)"
  and a2:    "!! \<Gamma> b T x. \<Delta>\<^isub>\<tau> b = T \<Longrightarrow> 
  (!! x t T \<Gamma> F. (t\<guillemotleft>BI b) \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> P x \<Gamma> (BI b) T NE"
  and a3:    "!! \<Gamma> n x.   (!! x t T \<Gamma> F. (t\<guillemotleft>Num n) \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> 
  P x \<Gamma> (Num n) ty.Int NE"
  and a4:    "!! \<Gamma> x.   (!! x t T \<Gamma> F. (t\<guillemotleft>Bool True) \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> 
  P x \<Gamma> (Bool True) BoolTy TT"
  and a5:    "!! \<Gamma> x. (!! x t T \<Gamma> F. (t\<guillemotleft>Bool False)  \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> 
  P x \<Gamma> (Bool False) BoolTy FF"
  and a6:    "\<And>\<Gamma> \<tau> \<sigma> t1 t2 x F1 F2 le \<tau>0 U. (!! x t T \<Gamma> F. (t\<guillemotleft>App t1 t2) \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> 
              \<Gamma> \<turnstile> t1 : U ; F1 \<Longrightarrow> \<turnstile> U <: \<tau>\<rightarrow>\<sigma>:le \<Longrightarrow> (\<And>z. P z \<Gamma> t1 U F1) \<Longrightarrow> \<Gamma> \<turnstile> t2 : \<tau>0 ; F2 \<Longrightarrow> (\<And>z. P z \<Gamma> t2 \<tau>0 F2) \<Longrightarrow> \<turnstile> \<tau>0 <: \<tau>
              \<Longrightarrow> P x \<Gamma> (App t1 t2) \<sigma> NE"
  and a7:    "\<And>a \<Gamma> \<tau> \<sigma> t x F0. a\<sharp>x \<Longrightarrow> a\<sharp>\<Gamma> \<Longrightarrow> ((a,\<tau>) # \<Gamma>) \<turnstile> t : \<sigma> ; F0 \<Longrightarrow> (\<And>z. P z ((a,\<tau>)#\<Gamma>) t \<sigma> F0) \<Longrightarrow>
              (!! x t' T \<Gamma> F. (t'\<guillemotleft>Lam[a:\<tau>].t) \<Longrightarrow> \<Gamma> \<turnstile> t' : T ; F \<Longrightarrow> P x \<Gamma> t' T F) 
              \<Longrightarrow> P x \<Gamma> (Lam [a:\<tau>].t) (\<tau>\<rightarrow>\<sigma>:latent_eff.NE) NE"
  and a8:    "\<And>\<Gamma> \<tau> \<sigma> t1 t2 x F1 \<tau>0 S v U. 
              (!! x t T \<Gamma> F. t \<guillemotleft> App t1 t2 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> 
              \<Gamma> \<turnstile> t1 : U ; F1 \<Longrightarrow> \<turnstile> U <: (\<tau>\<rightarrow>\<sigma>:Latent S) \<Longrightarrow> (\<And>z. P z \<Gamma> t1 U F1) \<Longrightarrow> \<Gamma> \<turnstile> t2 : \<tau>0 ; VE v \<Longrightarrow> 
              (\<And>z. P z \<Gamma> t2 \<tau>0 (VE v)) 
              \<Longrightarrow> \<turnstile> \<tau>0 <: \<tau>  \<Longrightarrow> P x \<Gamma> (App t1 t2) \<sigma> (TE S v)"
  and a9:    "!! \<Gamma> e1 e2 e3 T1 T2 T3 T eff1 eff2 eff3 x. 
                 \<lbrakk>\<Gamma> \<turnstile> e1 : T1; eff1; !!z. P z \<Gamma> e1 T1 eff1; (\<Gamma> |+ eff1) \<turnstile> e2 : T2; eff2; !!z. P z (\<Gamma>|+ eff1) e2 T2 eff2; 
                (!! x t T \<Gamma> F. t \<guillemotleft> Iff e1 e2 e3 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
                 (\<Gamma> |- eff1) \<turnstile> e3 : T3; eff3; !!z. P z (\<Gamma>|- eff1) e3 T3 eff3; \<turnstile> T2 <: T; \<turnstile> T3 <: T\<rbrakk>
                 \<Longrightarrow> P x \<Gamma> (Iff e1 e2 e3) T NE"
  and a10:   "!! \<Gamma> e1 e2 T0 T1 T S eff1 eff2 x U. 
              \<lbrakk>\<Gamma> \<turnstile> e1 : U; eff1; \<turnstile> U <: (T0 \<rightarrow> T1 : Latent S) ; !!z. P z \<Gamma> e1 U eff1;
              (!! x t T \<Gamma> F. t \<guillemotleft> App e1 e2 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
              \<Gamma> \<turnstile> e2 : T; eff2 ;  !! z. P z \<Gamma> e2 T eff2; \<turnstile> T <: T0; \<turnstile> T <: S\<rbrakk> \<Longrightarrow> P x \<Gamma> (App e1 e2) T1 TT"
  and a11:   "!! \<Gamma> e1 e2 T0 T1 T S eff1 eff2 x U. 
              \<lbrakk>\<Gamma> \<turnstile> e1 : U; eff1; \<turnstile> U <: (T0 \<rightarrow> T1 : Latent S) ; !!z. P z \<Gamma> e1 U eff1;
              (!! x t T \<Gamma> F. t \<guillemotleft> App e1 e2 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
              \<Gamma> \<turnstile> e2 : T; eff2 ;  !! z. P z \<Gamma> e2 T eff2; \<turnstile> T <: T0; ~(\<turnstile> T <: S) ; e2 : values ; closed e2\<rbrakk>
  \<Longrightarrow> P x \<Gamma> (App e1 e2) T1 FF"
  and a12:   "!! \<Gamma> e1 e2 e3 T T1 T2 eff x. \<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; TT ; !! z. P z \<Gamma> e1 T1 TT; 
                (!! x t T \<Gamma> F. t \<guillemotleft> Iff e1 e2 e3 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
               \<Gamma> \<turnstile> e2 : T2 ; eff;  !!z .P z \<Gamma> e2 T2 eff; \<turnstile> T2 <: T\<rbrakk> \<Longrightarrow> P x \<Gamma> (Iff e1 e2 e3) T NE"
  and a13:   "!! \<Gamma> e1 e2 e3 T T1 T3 eff x. \<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; FF ; !! z. P z \<Gamma> e1 T1 FF; 
                (!! x t T \<Gamma> F. t \<guillemotleft> Iff e1 e2 e3 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
               \<Gamma> \<turnstile> e3 : T3 ; eff;  !!z .P z \<Gamma> e3 T3 eff; \<turnstile> T3 <: T\<rbrakk> \<Longrightarrow> P x \<Gamma> (Iff e1 e2 e3) T NE"
  shows "P x \<Gamma> t T F"
  using a
  proof (nominal_induct t avoiding: x \<Gamma> T F rule: trm_comp_induct)
    case (Var v) 
    thus ?case using a1 var_ty_elim[of \<Gamma> v T F] by auto
  next
    case (App t1 t2 x \<Gamma> T)
    show ?case using App(4)
    proof (induct rule: app_ty_elim2)
      case 1 thus ?thesis using a6 App trm.inject ty.inject by auto
    next
      case 2 thus ?thesis using a8 App trm.inject ty.inject by auto
    next
      case 3 thus ?thesis using a10 App trm.inject ty.inject by auto
    next
      case 4 thus ?thesis using a11 App trm.inject ty.inject by auto
    qed
  next
    case Iff
    show ?case using Iff(5)
    proof (induct rule: iff_ty_elim2)
      case 1 thus ?thesis using a9 Iff trm.inject ty.inject by auto
    next
      case 2 thus ?thesis using a12 Iff trm.inject ty.inject by auto
    next
      case 3 thus ?thesis using a13 Iff trm.inject ty.inject by auto
    qed
  next
    case (Lam v b x \<Gamma> S1 F S2)
    show ?case using Lam abs_ty_elim[of \<Gamma> v b S2 S1 F] a7 by (auto simp add: trm.inject ty.inject)
  next
    case (BI b) thus ?case using bi_ty_elim[of \<Gamma> b T F] trm.inject a2 by auto
  next
    case (Num n) thus ?case using num_ty_elim[of \<Gamma> n T F] trm.inject a3 by auto
  next
    case (Bool b) thus ?case using true_ty_elim[of \<Gamma> T F] false_ty_elim[of \<Gamma> T F] trm.inject a4 a5 by (cases b) auto
qed


