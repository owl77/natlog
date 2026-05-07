import copy
import BLtokenizer

class Leaf:
 def __init__(self,name,type):
  self.name = name
  self.signature = None
  self.type = type
  self.free = True
  self.pos = -1
  self.variable = None
  self.variables = None
 
  self.prefix =True
class Constructor:
  def __init__(self,operator, type,children):     
   self.name ="constructor"
   self.operator = operator
   self.type= type
   self.children = children
   self.binary = False
   self.left = None
   self.right = None
   if len(children)==2:
    self.binary =True
    self.left = children[0]
    self.right = children[1]

def Star(parser,separator):
 def out(exp):    
     
  parse = parser(exp)      
  if parse!=None:
   return [parse]  
  if len(exp) < 3:
   return None
  if len( [x for x in separator if x in exp] ) == 0:
      return None
   
  length = len(exp) 
  for i in range(1,length-1):  
    if not exp[i] in separator:
     continue  
    par1 =  parser(exp[0:i])   
    
    if par1== None:
      continue
    #if not exp[i] in separator:
    # continue
    par2 =  Star(parser,separator)(exp[i+1:])
    if par2 == None:
      continue
    return [par1] + par2
 return out


def Binary(parser1,parser2, opparser):
 def out(exp):
  length = len(exp)     
  if length < 5:
   return None
  for i in range(2,length-2):
   opars = opparser([exp[i]])      
   if opars ==None:
     continue
   if  exp[0]!="(" or exp[length-1]!=")":
     continue
   par1 =  parser1(exp[1:i])
   if par1== None:
     continue
   par2 =  parser2(exp[i+1:length-1])
   if par2 == None:
      continue
   aux = Constructor(opars,opars.type,[par1,par2])
   if len(opars.signature)!=2:
     return None
   if opars.signature[0]!=aux.left.type or opars.signature[1]!= aux.right.type:
     return None
   return aux
 return out

def Operator(opparser, parser, separator,parenthesis):
 if parenthesis==True:
  def out(exp):
   if len(exp) < 4:
    return None
   for i in range(1,len(exp)-2):
       
    if  exp[i]!="(" or exp[len(exp)-1]!=")":
     continue
    opars =  opparser(exp[0:i])
    if opars == None:
        continue
    star = Star(parser,separator)(exp[i+1:len(exp)-1])
    if star == None:
     continue    
    
    if len(star)!=len(opars.signature):
      return 
    for i in range(0,len(star)):
     if star[i].type!=opars.signature[i]:
       return
    return Constructor(opars, opars.type,star)
    
  return out
 else:
  def out(exp):
   if len(exp) < 2:
    return 
   for i in range(1,len(exp)):
    aux1 = copy.deepcopy(exp)   
    opars = opparser(aux1[0:i])
    if opars == None:
        continue
    star = Star(parser,separator)(aux1[i:])
   
    if star == None:
        continue
    if len(star)!=len(opars.signature):
      return
    for i in range(0,len(star)):
      if star[i].type!=opars.signature[i]:
       return
    return Constructor(opars, opars.type,star)
    
  return out


def Or(parserlist):
 def out(exp):
  for i in range(0,len(parserlist)):
    par =  parserlist[i](exp) 
    if par!=None:
      return par
 return out


   
def TruePrintout(ast):
    if type(ast).__name__=="Leaf":
     return ast.name
    if type(ast).__name__=="Constructor":
     aux = [TruePrintout(x) for x in ast.children]
     if ast.operator.name =="&":
        return "(" + aux[0]+ " "+TruePrintout(ast.operator) + " "+aux[1]+")"
     if ast.operator.name =="neg":
         return "neg " + aux[0]    
     if ast.operator.name =="forall":
         return TruePrintout(ast.operator) + " "+TruePrintout(ast.operator.variable) + "." + aux[0]
     if ast.operator.name =="lambda":
         return TruePrintout(ast.operator) + " "+ ",".join([TruePrintout(x) for x in ast.operator.variables])+ "." + aux[0]
     return TruePrintout(ast.operator) +"("+(",").join(aux)+")"
 
     
binders = {"forall":{"sourcetypes":["Formula"], "targettype":"Formula"}}
multibinders = {"lambda":{"sourcetypes":["Formula"], "targettype":"Term"}}

constants = []
variables = ["x","y","z","u","v","w","f","g","h","r"]
predicates = {"A":{"sourcetypes":["Term","Term"],"targettype":"Formula","prefix": False},"B":{"sourcetypes":["Term","Term", "Term"],"targettype":"Formula","prefix": False} }
operators = {"&":{"sourcetypes":["Formula","Formula"],"targettype":"Formula","prefix":False}}
modal = {"neg": {"sourcetypes":["Formula"],"targettype":"Formula"}}



def BinderParser(binders,variableparser):
 def out(exp):     
  if len(exp) < 3 or len(exp) > 3:
   return None
  if exp[1] in constants:
    return None   
  if exp[0] in binders.keys() and variableparser([exp[1]])!=None and exp[2]==".":       
   aux = Leaf(exp[0], binders[exp[0]]["targettype"])
   aux.variable = variableparser([exp[1]])
   aux.signature = binders[exp[0]]["sourcetypes"]
   return aux
 return out


def Simple(list, type):
 def out(exp):
  if len(exp)!=1:
    return None
  if exp[0] in list:
   return Leaf(exp[0], type)
 return out
 

def SimpleCons(dic):
 def out(exp):
  if len(exp)!=1:
   return None
  if exp[0] in dic.keys():
   aux = Leaf(exp[0],dic[exp[0]]["targettype"])
   aux.signature = dic[exp[0]]["sourcetypes"]
   if len(aux.signature)== 2:
    aux.prefix = dic[exp[0]]["prefix"]            
   return aux
 return out

 
def ArityToTypes(n):
 if n == 0:
  return []
 aux = ["Term"] + ArityToTypes(n-1)
 return aux     


MultiVariableParser = Star(Simple(variables, "Term"), [","])


#better def MultiBinderParser(multibinders, variablelistparser)

def MultiBinderParser():
 def out(exp):     
  if len(exp) < 2:
   return None
  if not exp[len(exp)-1] ==".":
   return None
  if exp[0] in multibinders.keys():
    if len(exp)==2:
     o =   Leaf(exp[0], multibinders[exp[0]]["targettype"])
     o.signature = multibinders[exp[0]]["sourcetypes"]
     o.variables = []
     return o
    trim = exp[1:len(exp)-1]
    
    aux = MultiVariableParser(trim)
    if aux!=None:
     rep = [x.name for x in aux]
     if len(set(rep))!=len(rep):
       return None
     o =   Leaf(exp[0], multibinders[exp[0]]["targettype"])
     o.signature = multibinders[exp[0]]["sourcetypes"]
     o.variables = aux
     return o
 return out


def MultiBinderExp(parser):
 def out(exp):
  if len(exp) < 6:
   return None
  for i in range(2, len(exp)):
   aux1 = MultiBinderParser()(exp[0:i])
   if aux1==None:
     continue
   aux2 = parser(exp[i:])
   if aux2==None: 
      continue
   else:
      return Constructor(aux1, aux1.type, [aux2])
 return out
  
   
def Term(exp): 
 if len(exp) == 1 and exp[0] in variables:
    return Simple(variables,"Term")(exp)
 if exp[0] =="lambda":
     aux= MultiBinderExp(Formula)(exp)
     if aux!=None:
       return aux
     aux2 = MultiBinderExp(Term)(exp)
     if aux2!= None and len(aux2.operator.variables) <= 1 and type(aux2.children[0]).__name__=="Leaf":
       return aux2

def Formula(exp):
  if len(exp) <=1:
      return None
            
  if exp[0] in ["forall"]:
      return Operator(BinderParser(binders,Simple(variables,"Term")), Formula ,[","],False)(exp)
     
  if exp[0] in predicates.keys():
      return Operator(SimpleCons(predicates),Term, [","],True)(exp)
   
  if exp[0] =="neg":
       return Operator(SimpleCons(modal),Formula, [","],False)(exp)
      
  test =   Binary(Formula,Formula, SimpleCons(operators))(exp)
  if test!= None:
          return test
  test =    Binary(Term,Term, SimpleCons(predicates))(exp)
  if test!=None:
         return test       
  return test
                                    

def termtest(exp):
 return Term(BLtokenizer.Tokenize(exp))    

def formtest(exp):
  return Formula(BLtokenizer.Tokenize(exp))    

