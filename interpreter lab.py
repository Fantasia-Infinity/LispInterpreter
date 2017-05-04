# -*- coding: utf-8 -*-
"""
Created on Thu Mar 16 22:27:07 2017

@author: Fantasia
"""
import re
def kong(exp):
    for cha in exp:
        if(cha=='(' or cha==')' or cha=='[' or cha==']'):
            exp=exp.replace(cha," "+cha+" ")
    return exp
def token(exp):
    exp=kong(exp).split()
    return exp
def findp(lis,i):#支持两种括号
    i+=1
    a=0
    while i<=len(lis)-1:
        if lis[i]=="(" or lis[i]=='[':
            a+=1
            i+=1
        elif lis[i]==")" or lis[i]==']':
            if a==0:
                break
            elif a!=0:
                a-=1
                i+=1
        else:
            i+=1
    return i
def parse(exp):
    def atom(exp):
        if len(exp)==1:
            return True
    if atom(exp):
        return exp
    elif(exp==[]):
        return []
    elif(exp[0]=="(" or exp[0]=="["):
        sexp=exp[1:findp(exp,0)]
        return [parse(sexp)]+parse(exp[findp(exp,0)+1:])
    elif(exp[0]!="(" or exp[0]!="["):
        return [exp[0]]+parse(exp[1:])
def parser(exp):
        return parse(exp)[0]
def list_of_values(args,env):
    return [evall(x,env) for x in args]
def cons(a,b):
    return (a,b)
def car(p):
    return p[0]
def cdr(p):
    return p[1]
def listt(*a):
    if len(a)==0:
        return ()
    else:
        return cons(a[0],listt(*tuple(a[1:])))
def add(*a):
    s=a[0]
    for n in a[1:]:
        s=s+n
    if len(a)!=0:
        return s
    else:
        return add
def mul(*a):
    s=1
    for n in a:
        s*=n
    if len(a)!=0:
        return s
    else:
        return mul
def minus(a,b):
    return a-b
def div(a,b):
    return a/b
def equ(*a):
    if(len(a)==1):
        return True
    elif(a[0]!=a[1]):
        return False
    elif(a[0]==a[1]):
        return equ(*tuple(a[1:]))
def andd(*a):
    if(len(a)==0):
        return True
    elif(a[0]==True):
        return andd(*tuple(a[1:]))
    elif(a[0]==False):
        return False
def orr(*a):
    if True in a:
        return True
    else:
        return False
def less(a,b):
    return a<b
def split(a):
    return a.split()
pripro={"+":add,"-":minus,"*":mul,"/":div,"true":True,"false":False}
pripro["="]=equ
pripro["and"]=andd
pripro["or"]=orr
pripro["<"]=less
pripro["cons"]=cons
pripro["car"]=car
pripro["cdr"]=cdr
pripro["list"]=listt
pripro["split"]=split
global_env=[pripro]
g=global_env
def extend_env(variables,values,env):#用于复合过程求值
    return [dict(zip(variables,values))]+env
def add_env(var,arg,env):#用于define
    env[0][var]=arg
    return
def is_num(str):
    p="(\\-)?[0-9]+(//.)?[0-9]*"#支持小数和负数
    if re.search(p,str):
        return True
    elif str.isdigit():
        return True
    else:
        return False
def is_self_eval(ir):#还只有数字和布尔值
    return (type(ir)==str and (is_num(ir) or ir=="True" or ir=="False" or ir[0]==ir[-1]=="'"))
def eval_self(ir):#还只有数字和布尔值
    if(is_num(ir)):
        return eval(ir)
    elif(ir in global_env):
        return global_env[ir]
    elif(ir[0]==ir[-1]=="'"):
        return ir
def is_application(ir):#这种粗糙的判法必须要放到evall的最后，不然误判
    return (len(ir)!=1)
def is_definition(ir):
    return (ir[0]=="define")
def eval_definition(ir,env):
    if(type(ir[1])==str):
        val=evall(ir[2],env)
        add_env(ir[1],val,env)
    elif(type(ir[1])==list):
        m=make_lambda(ir[1],ir[2],env)
        em=evall(m,env)
        add_env(ir[1][0],em,env)
    return
def make_lambda(s,body,env):
    return ['lambda',s[1:],body]
def look_up(var,env):
    if(env==[]):
        print "No found"
    elif(var in env[0]):
        return env[0][var]
    else:
        return look_up(var,env[1:])
def is_variable(ir):
    return (type(ir)==str and (not is_self_eval(ir)))
def is_lambda(ir):
    return (ir[0]=="lambda")
def make_procedure(lambda_ir,env):
    return [lambda_ir[1],lambda_ir[2],env] 
def is_pri_pro(procedure):
    return (not is_com_pro(procedure))
def is_com_pro(procedure):
    if(type(procedure)==list):
        return True
    else:
        return False
def is_if(ir):
    return (ir[0]=='if')
def eval_if(ir,env):
    condition=ir[1]
    then=ir[2]
    elsee=ir[3]
    if(evall(condition,env)):#直接沿袭python的True/False判断
        return evall(then,env)
    else:
        return evall(elsee,env)
def is_cond(ir):
    return (ir[0]=="cond")
def eval_cond(ir,env):
    condlist=ir[1:]
    for item in condlist:
        if(item[0]=="else"):
            return evall(item[1],env)
        elif(evall(item[0],env)==True):
            return evall(item[1],env)
            break
def is_quote(ir):
    return (ir[0]=="quote")
def ir_to_tuple(ir):
    if(type(ir)==str):
        return ir
    elif(type(ir)==list and len(ir)>1):
        return cons(ir_to_tuple(ir[0]),ir_to_tuple(ir[1:]))
    elif(type(ir)==list and len(ir)==1):
        return cons(ir_to_tuple(ir[0]),())
def is_setq(ir):
    return (ir[0]=="set!")
def eval_setq(ir,env):
    va=ir[1]
    def is_in_env(var):
        for s in env:
            if var in s:
                return True
        return False
    if(is_in_env(va)):
        for s in env:
            if va in s:
                s[va]=evall(ir[2],env)
                return
    else:
        env[0][va]=evall(ir[2],env)
def is_eval(ir):
    return (ir[0]=="eval")
def eval_eval(ir,env):#将要eval的quote表达式ir重新做成lisp表达式再送回来token，parser后再evall()
    return evall(parser(token(ttp((evall(ir[1],env))))),env)
def is_apply(ir):
    return (ir[0]=="apply")
def eval_apply(ir,env):
    return evall(parser(token(ttp(cons(ir_to_tuple(ir[1]),evall(ir[2],env))))),env)
def eval_seq(irl,env):
    l=[evall(i,env) for i in irl]
    return l[-1]
def is_begin(ir):
    return ir[0]=='begin'
def eval_begin(ir,env):
    return eval_seq(ir[1],env)
def evall(ir,env):
    if(is_self_eval(ir)):
        return eval_self(ir)
    elif(is_definition(ir)):
        return eval_definition(ir,env)
    elif(is_lambda(ir)):
        return make_procedure(ir,env)
    elif(is_variable(ir)):
        return look_up(ir,env)
    elif(is_begin(ir)):
        return eval_begin(ir,env)
    elif(is_if(ir)):
        return eval_if(ir,env)
    elif(is_cond(ir)):
        return eval_cond(ir,env)
    elif(is_quote(ir)):
        return ir_to_tuple(ir[1])
    elif(is_setq(ir)):
        return eval_setq(ir,env)
    elif(is_eval(ir)):
        return eval_eval(ir,env)
    elif(is_apply(ir)):
        return eval_apply(ir,env)
    elif(is_application(ir)):
        return applyy(evall(ir[0],env),list_of_values(ir[1:],env))
def applyy(procedure,args):
    if(is_pri_pro(procedure)):
        return (procedure(*tuple(args)))
    elif(is_com_pro(procedure)):
        new_ir=procedure[1]
        new_env=extend_env(procedure[0],args,procedure[2])
        return evall(new_ir,new_env)
def DiveIntoLisp():
    while True:
        exp=raw_input(">")
        if(exp=='Awake'):
            return
        exp=parser(token(exp))
        output=evall(exp,g)
        if(output is None):
            print 'ok'
        elif(type(output)==tuple):#lisp中列表和quote的内部表示为tuple，但在显示的时候转换成lisp表示中相应的字符串
            print ttp(output)
        else:
            print output
def tuple_to_lisp(tir):
    if type(tir) != tuple:
        return str(tir)+' '#显示的时候各种类型的值都变成字符串来显示
    elif tir==():
        return ''
    elif type(car(tir))==tuple:
        return '('+tuple_to_lisp(car(tir))+')'+' '+tuple_to_lisp(cdr(tir))
    else:
        return tuple_to_lisp(car(tir))+' '+tuple_to_lisp(cdr(tir))
def ttp(tir):
    r= '('+tuple_to_lisp(tir)+')'
    r=r.replace(' )',')')
    r=r.replace('  )',')')
    if type(tir) is str:
        return tir
    else:
        return r
    

DiveIntoLisp()

    
    
    
    
    
