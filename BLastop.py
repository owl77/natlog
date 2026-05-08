
import BLparser
import BLtokenizer
import weavers
import ntl 
import copy

def Free(ast,varnames):
 if type(ast).__name__=="Leaf":
   if not ast.name in varnames:
    ast.free = True
    return ast
   else:
    ast.free = False
    return ast
 else:
  if not ast.operator.name in ["forall","lambda"]:
   oldchildren = ast.children
   ast.children = [Free(x,varnames) for x in oldchildren]
   return ast
  else:
   if ast.operator.name =="forall":
    newnames = varnames + [ast.operator.variable.name]
    oldchildren = ast.children
    ast.children = [Free(x,newnames) for x in oldchildren]
    return ast
   else:
    newnames = varnames + [x.name for x in ast.operator.variables]
    oldchildren = ast.children
    ast.children = [Free(x,newnames) for x in oldchildren]
    return ast


def VarSubstitution(ast,oldname,freshname):
 if type(ast).__name__=="Leaf":
  if ast.free ==True and ast.name == oldname:
   ast.name = freshname
   return ast
  else:
   return ast
 else:
  oldchildren = copy.deepcopy(ast.children)
  ast.children=[VarSubstitution(x,oldname,freshname) for x in oldchildren]
  return ast

def Passing(list, func, n):
 if len(list)==0:
  return [[],n]
 if len(list)==1:
  return [[func(list[0],n)[0]], func(list[0],n)[1]]
 else:
  aux = func(list[0],n)
  aux2 = Passing(list[1:], func, aux[1])
  return [[aux[0]]+ aux2[0], aux2[1]]
                   
       

def BoundVariableChange(ast,oldname,newname):
 if type(ast).__name__=="Leaf":
  return ast
 else:
  if ast.operator.name in ["forall"]:
   if ast.operator.variable.name==oldname:
    ast.operator.variable.name=newname
    aux = [VarSubstitution(Free(x,[]),oldname,newname) for x in ast.children]
    ast.children = [BoundVariableChange(x,oldname,newname) for x in aux]
    return ast
   else:
    ast.children = [BoundVariableChange(x,oldname,newname) for x in ast.children]  
    return ast
  if ast.operator.name in ["lambda"]:
   names =  [x.name for x in ast.operator.variables]
   if oldname in names:
    i = names.index(oldname)
    ast.operator.variables[i].name = newname 
    aux = [VarSubstitution(Free(x,[]),oldname,newname) for x in ast.children]
    ast.children = [BoundVariableChange(x,oldname,newname) for x in aux]
    return ast
   else:
    ast.children = [BoundVariableChange(x,oldname,newname) for x in ast.children]  
    return ast
  return ast

    


def BasicSubstitution(ast,old,fresh):
 if type(ast).__name__=="Leaf":
    if ast.free!=True:
      return ast    
    if ast.name == old.name:      
      return fresh
 if type(ast).__name__=="Leaf":
  return ast
 else:
  oldchildren = ast.children
  ast.children=[BasicSubstitution(x,old,fresh) for x in oldchildren]
  if len(ast.children)==2:
    ast.left = ast.children[0]
    ast.right = ast.children[1]  
  return ast



def GetFreeVars(ast,typ):
 if type(ast).__name__== "Leaf":
  if ast.free==True and ast.type==typ and not ast.name in BLparser.constants:
   return [ast.name]
  else:
   return []
 else:
   aux =[GetFreeVars(x,typ) for x in ast.children]
   aux2 = []
   for x in aux:
    for y in x:
     aux2.append(y)
   return aux2
#this should preserve the order, useful for Bealer's logic.

  
def GetBindVars(ast):
 if type(ast).__name__=="Leaf":
  return []
 else:
  if ast.operator.name in ["forall"]:
   aux3 = [ast.operator.variable.name]
  if ast.operator.name in ["lambda"]:
   aux3 = [x.name for x in ast.operator.variables]
  else:
   aux3=[]
  aux2 =[GetBindVars(x) for x in ast.children]
  for x in aux2:
   for y in x:
    aux3.append(y) 
  return aux3

def Substitution(ast,var,term):
  free = GetFreeVars(term,"Term")
  
  bind = GetBindVars(ast)
  
  subs = [x for x in bind if x in free]
  
  for y in subs:
   y2 = tokenizer.Fresh(BLparser.variables,BLtokenizer.alphabet)
   
   ast = BoundVariableChange(ast,y, y2)
   
   BLparser.variables.append(y2)
   
  return BasicSubstitution(ast,var,term)



def MultiFresh(n):
 out = []   
 for m in range(0,n):
   newvar = BLtokenizer.Fresh(BLparser.variables,tokenizer.alphabet)         
   BLparser.variables.append(newvar)
   out.append(newvar)
 return out
  

def MultiSub(form,oldnamelist,newtermlist):
 #must check for clashes    
 aux = form
 for k in range(0,len(oldnamelist)):  
  aux = Substitution(form,BLparser.Term(BLtokenizer.Tokenize(oldnamelist[k])) , newtermlist[k])
 return aux      



def matrixlambdaboundchange(termlist):
 i = 0
 used = []
 newtermlist = []
 l = []
 for t in termlist:
  aux = t.operator.variables
  h = copy.deepcopy(t)
  
  for v in aux:
     
     if v.name in used:
       newname = v.name + str(i)
       BLparser.variables.append(newname)
       
       
       
       
       h= BoundVariableChange(h, v.name, newname)
       
  i = i + 1  
  l.append(h)     
  used = used + [x.name for x in aux]
 return l
# Operations for Bealer logic

def makelambda(variables, body):
 lambdaleaf = BLparser.Leaf("lambda", "Term")
 lambdaleaf.variables = variables
 return BLparser.Constructor(lambdaleaf, "Term" , [body])

def up(w,t):
 if not weavers.isWeaver(w):
  return None
 if type(t).__name__ == "Leaf":
  return None
 if t.operator.name!="lambda":
  return None
 if not len(w[0])== len(t.operator.variables):
  return None 
 oldnames = [x.name for x in t.operator.variables]
 newweaver = weavers.weaverShift(w, oldnames)
 sharp = weavers.weaverSharp(newweaver)
 snew =  ["{"+''.join(x) + "}" for x in sharp]
 snew2 = ["{"+''.join(x) + "}" for x in newweaver[1]]
 BLparser.variables = BLparser.variables +  snew2
 newvars = [BLparser.Term(BLtokenizer.Tokenize(x)) for x in snew]
 newvars2 = [BLparser.Term(BLtokenizer.Tokenize(x)) for x in snew2]
 out = Free(copy.deepcopy(t.children[0]),[])
 out2 = MultiSub(out, oldnames, newvars)
 return makelambda(newvars2, out2)

def pi(seq, head, rawbody):
  #boring type checking - don't forget x -> lambda .x change
  for t in rawbody:
   if type(t).__name__=="Leaf":
     t = makelambda([],t)  
  body = matrixlambdaboundchange(copy.deepcopy(rawbody))
  if len(seq)!= len(head.operator.variables) or len(seq)!=len(body):
   return None
  for i in range(0, len(seq)):
   if len(body[i].operator.variables)< seq[i]:
    return None
  newvarlists = []
  newterms = []
  oldvarnamelist = [x.name for x in head.operator.variables]
  for i in range(0,len(seq)):
   newvarlists = newvarlists + body[i].operator.variables[0:seq[i]]
   newterms.append(Free(makelambda(body[i].operator.variables[seq[i]:], body[i].children[0]),[]) )
  aux1 = Free(copy.deepcopy(head.children[0]),[])
  aux2 = [ Free(copy.deepcopy(x),[]) for x in newterms]
  aux = MultiSub(aux1, oldvarnamelist , aux2)
  return makelambda(newvarlists, aux)

def ln(term):
 aux = BLparser.TruePrintout(term.children[0])
 aux2 = BLparser.formtest("neg " + aux)
 return makelambda(term.operator.variables, aux2)

def la(term1,term2):
 newvars = term1.operator.variables + term2.operator.variables
 aux1 = BLparser.TruePrintout(term1.children[0])
 aux2 = BLparser.TruePrintout(term2.children[0])
 aux3 = BLparser.formtest("(" + aux1 + " & " + ")")
 return makelambda(newvars, aux3)
 
def lq(term):
 aux = BLparser.TruePrintout(term.children[0])
 var = term.operator.variables[0].name
 aux2 = BLparser.formtest("forall " + var + "." + aux)
 return makelambda(term.operator.variables[1:], aux2)

def nicebound(term):
 bounds = GetBindVars(term) + GetFreeVars(term,"Term")
 newvars = [x for x in BLparser.variables if not x in bounds ]
 oldbinds = term.operator.variables
 if len(newvars) >= len(oldbinds):
  aux = copy.deepcopy(term)
  for i in range(0,len(oldbinds)):
   aux = BoundVariableChange(aux, oldbinds[i].name, newvars[i])
  return aux
 return term

def BealerWeaver(l,input):
 #input must be a list of sets
 if not weavers.isListOfSets(input) or weavers.isListOfLists(input):
  return None
 if not weavers.uniqueList(l):
   return None 
 aux = []
 seq = []
 for group in input:
  aux = aux + [s for s in l if s in group]
  seq = seq + [len([s for s in l if s in group])]
 aux2 = weavers.canonicalWeaver(aux,l)
 return {"weaver": aux2, "list" : aux, "partition": weavers.sequenceToPartition(list(range(0,len(aux2[0]))),seq)}
 #input defines an order partition on the canonical weaver. Clearly aux2 is without this partition.

 
def isPrimitive(term):
 if len(term.operator.variables) != len(term.children[0].children):
  return False 
 for i in range(0, len(term.operator.variables)):
    if not type(term.children[0].children[i]).__name__ =="Leaf":
     return False 
    if term.children[0].children[i].name != term.operator.variables[i].name:
     return False 
 return True 


def BealerStep(term):
 if type(term).__name__ == "Leaf":
  return term
 if type(term.children[0]).__name__ =="Leaf":
   return term
 if isPrimitive(term):
  return term
   
 if term.children[0].operator.name not in ["lambda", "forall", "neg", "&"]:
  args = term.operator.variables
  varl = []
  newvarl = []
  arity = len(term.children[0].children)
  primitive = term.children[0].operator 
  for t in term.children[0].children:
   varl.append([v for v in args if v in getFreeVars(t,"Term")])
  for i in range(0,arity): 
   newvarl.append( varl[i] + term.children[0].children.operator.variables)
  seq = weavers.listUnion(varl)
  bw = BealerWeaver(args, seq)
  newterms = []
  for s in range(0,arity):
   newterms.append(makelambda(newvarl[i],term.children[0].children[i].children[0]   ))
  head = copy.deepcopy(term)
  head.operator.variables = head.operator.variables[0:arity]
  head.children[0].children = head.operator.variables 
  return [head, newterms]
  #case for neg, &, forall and lambda .x and lambda x.x 



def Numeric(ast,n):
 if type(ast).__name__=="Leaf":
  return ast
 else:
  if ast.operator.name in ["exists"]:
   var = ast.operator.variable.name
   ast.operator.variable.name = str(n)
   aux = VarSubstitution(Free(ast.children[0],[]), var, str(n)) 
   ast.children = [Numeric(aux, n+1)]
   return ast
  if ast.operator.name in ["lambda"]:
   b = len(ast.operator.variables)
   newv = ast.operator.variables
   body = ast.children[0]
   for j in range(0,b):
    
    body = VarSubstitution(Free(body,[]), ast.operator.variables[j].name, str(n+j))
    newv[j].name = str(n+j)
   body2 = Numeric(body,n+j)
   return makelambda(newv, body2)
  else:
   aux = [Numeric(x,n) for x in ast.children]
   ast.children = aux
   return ast

def FastEquals(ast1,ast2):
    if type(ast1).__name__=="Leaf":
      if type(ast2).__name__=="Leaf":
        return ast1.name == ast2.name
    else:
     if type(ast2).__name__=="Constructor":      
       if ast1.operator.name != ast2.operator.name:
           return False
       if len(ast1.children)!= len(ast2.children):
           return False
       for x in range(0,len(ast1.children)):
          if not FastEquals(ast1.children[x], ast2.children[x]):
              return False      
       return True
     return False
         

def Equals(ast1,ast2):
  a1 = copy.deepcopy(ast1)
  a2 = copy.deepcopy(ast2)    
  aux1 = Numeric(a1,0)
  aux2 = Numeric(a2,0)
  
  #return parser.TruePrintout(aux1) == parser.TruePrintout(aux2)
  return FastEquals(aux1,aux2)

 




