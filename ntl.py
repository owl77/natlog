
import weavers


#tokenizer

def SpaceParenthesis(form):
  if form == None or form =="":
   return ""
  if form[0] in ["{","}",",","(",")"]:
   return " " + form[0] + " " +SpaceParenthesis(form[1:])
  else:
   return form[0] + SpaceParenthesis(form[1:])


def Clean(f):
 def aux(form):
  if form[0]==" ":
    return form[1:]
  if form[len(form)-1]==" ":
    return form[0:len(form)-1]
  for i in range(0,len(form)-1):
   if form[i:i+2] =="  ":
     return form[0:i] + form[i+1:]
  return form
 while f!=aux(f):
  f = aux(f)
 return f

def Fix(form):
 return Clean(SpaceParenthesis(form)) 

def Tokenize(form):
 return Fix(form).split(" ")


class PrimitiveTerm:
 def __init__(self, name, valency):
  self.name = name
  self.valency = valency
  self.pos = 0

class ConstructedTerm:
 def __init__(self, constructor, param,  args):
  self.constructor = constructor
  self.param = param
  self.args = args
  self.valency = None
  self.pos = 0

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


def Star2(parser,separator,op,cl):
 def out(exp):   
      
 #if not separator in exp:
  #   return None

  if len(exp)<2:
    return None       
  if exp[0]!=op:
      return None
  if exp[len(exp)-1 ]!=cl:
      return None
  trim = exp[1: len(exp)-1]
  aux = Star(parser,[separator])(trim)

  return aux
 return out


def parserConcat(parser1,parser2):
 def aux(exp):
  

  if len(exp) < 2:
    return None
  for i in range(1, len(exp)):
   
   a = parser1(exp[0:i])
   
   if a==None:
    continue
   b = parser2(exp[i:])
   
   if b==None:
    continue
   
   return [a,b]
  
 return aux


def Star3(parser):
 def out(exp):
  if len(exp)== 0:
   return None   
  parse = parser(exp)      
  if parse!=None:
   return [parse]  
   
  length = len(exp) 
  for i in range(1,length):  
    par1 =  parser(exp[0:i]) 
    if par1== None:
      continue
    par2 =  Star3(parser)(exp[i:])
    if par2 == None:
      continue
    return [par1] + par2
    
 return out

def parserSimple(a):
 def out(l):
  if not type(l)==list:
   return None
  if not len(l) == 1:
   return None
  if not l[0] ==a:
   return None
  return a
 return out



def parserPosInt(l):
 if not type(l)==list:
  return None
 if not len(l) == 1:
  return None
 if not l[0].isdigit(): 
  return None
 if not int(l[0]) > 0:
  return None
 return int(l[0])

def parserPosZeroInt(l):
 if not type(l)==list:
  return None
 if not len(l) == 1:
  return None
 if not l[0].isdigit(): 
  return None
 if not int(l[0]) >= 0:
  return None
 return int(l[0])


def parserPiParam(p):
 return Star2(parserPosZeroInt,",","(",")")(p)


def parserSetPosInt(l):
 aux = Star2(parserPosInt,",","{","}")(l)
 if not aux==None:
  return set(aux)
 return None

def parserUpParam(p):
 aux = Star3(parserSetPosInt)(p)
 if aux!= None:
  aux2 = weavers.getSetofORel(aux)
  if aux2!=None:
    return [aux2,aux]
 return None

def parserLnParam(p):
 return parserPosZeroInt(p)

def parserLaParam(p):
 if len(p)!=5:
   return None
 if p[0]!="(" or p[4]!=")" or p[2]!=",":
   return None
 aux1 = parserPosZeroInt([p[1]])
 if aux1!= None:
   aux2 = parserPosZeroInt([p[3]])
   if aux2!= None:
    return [aux1,aux2]


def parserLqParam(p):
 return parserPosInt(p)

Primitives = {"I":1, "A":0, "B": 1, "C":2, "D":5, "E":3 }

def parserPrimitiveTerm(l):
  if not type(l)==list:
   return None
  if not len(l) == 1:
   return None
  if not l[0] in Primitives.keys():
   return None
  return PrimitiveTerm(l[0], Primitives[l[0]])

def valency(s):
 if type(s).__name__ == "PrimitiveTerm":
  return Primitives[s.name]
 if type(s).__name__ == "ConstructedTerm":
  if s.constructor == "Pi":
   return weavers.sumList(s.param)
  if s.constructor == "Up":
   return len(s.param[1])
  if s.constructor == "Ln":
   return s.param
  if s.constructor == "La":
   return s.param[0] + s.param[1]
  if s.constructor == "Lq":
   return s.param - 1


def PreparserPi(l):
 if len(l) < 2:
  return None
 return parserConcat(parserSimple("Pi"), parserPiParam)(l)

def parserPi(l,par):
 if len(l) < 6:
  return None
 aux = parserConcat(PreparserPi, Star3(par))(l)
 if aux!= None:
  if len(aux[1]) < 2:
   return None
  param = aux[0][1]
  n = valency(aux[1][0])
  if len(param) == n and len(aux[1][1:]) == n:
   for i in range(0,n):
    if param[i] > valency(aux[1][i+1]):
     return None
   return ConstructedTerm("Pi", param, aux[1])
 return None

def PreparserUp(l):
 if len(l) < 2:
  return None
 return parserConcat(parserSimple("Up"), parserUpParam)(l)

def parserUp(l,par):
 if len(l) < 3:
   return None
 aux = parserConcat(PreparserUp,  par)(l)
 if aux!= None:
  param = aux[0][1]
  n = valency(aux[1])
  if len(param[0]) == n:
   return ConstructedTerm("Up", param, aux[1])
 return None


def PreparserLn(l):
 if len(l) < 2:
  return None
 return parserConcat(parserSimple("Ln"), parserLnParam)(l)

def parserLn(l,par):
 if len(l) < 3:
  return None
 aux = parserConcat(PreparserLn,  par)(l)
 if aux!= None:
  param = aux[0][1]
  n = valency(aux[1])
  if param == n:
   return ConstructedTerm("Ln", param, aux[1])
 return None

def PreparserLq(l):
 if len(l) < 2:
  return None
 return parserConcat(parserSimple("Lq"), parserLqParam)(l)

def parserLq(l,par):
 if len(l) < 3:
   return None
 aux = parserConcat(PreparserLq,  par)(l)
 if aux!= None:
  param = aux[0][1]
  n = valency(aux[1])
  if param == n:
   return ConstructedTerm("Lq", param, aux[1])
 return None

def PreparserLa(l):
 if len(l) < 2:
  return None
 return parserConcat(parserSimple("La"), parserLaParam)(l)

def parserLa(l,par):
 if len(l) < 7:
  return None
 aux = parserConcat(PreparserLa,  parserConcat(par,par))(l)
 if aux!= None:
  param = aux[0][1]
  n = valency(aux[1][0])
  m = valency(aux[1][1])
  if param[0] == n and param[1] == m:
   return ConstructedTerm("La", param, aux[1])
 return None

  
def parserTerm(l):
  if len(l) == 0:
   return None
  aux = parserPrimitiveTerm(l)
  if aux!=None:
    return aux
  aux = parserUp(l,parserTerm)
  if aux!=None:
     return aux
  aux = parserLn(l, parserTerm)
  if aux!=None:
     return aux
  aux = parserLq(l, parserTerm)
  if aux!=None:
     return aux
  aux = parserLa(l, parserTerm)
  if aux!=None:
    return aux
  aux = parserPi(l,parserTerm)
  if aux!=None:
     return aux

  return None

def Term(s):
 return parserTerm(Tokenize(s))

def subTerms(s):
 aux = []
 for i in range(0, len(s)):
  for j in range(i+1, len(s)+1):

   a = parserTerm(s[i:j])
   if a!=None:
    aux = aux + [a]
 return aux

def subTerms2(s):
 aux = []
 if type(s).__name__ == "PrimitiveTerm":
  return [s]
 if type(s).__name__ == "ConstructedTerm":
  aux = aux + [s]
  if s.constructor in ["Pi", "La"]:
    for u in s.args:
      
      aux = aux + subTerms2(u)
     
    return aux
  else:
    
    aux = aux + subTerms2(s.args)
    return aux
 return aux


 
def Passing(list, func, n):
 if len(list)==0:
  return [[],n]
 if len(list)==1:
  return [[func(list[0],n)[0]], func(list[0],n)[1]]
 else:
  aux = func(list[0],n)
  aux2 = Passing(list[1:], func, aux[1])
  return [[aux[0]]+ aux2[0], aux2[1]]


def SubTermPosition(s,n):
 
 if type(s).__name__ == "PrimitiveTerm":
  s.pos = n
  return [s,n+1]  
 if type(s).__name__ == "ConstructedTerm":
  if s.constructor == "Pi":
   s.pos = n
   aux = Passing(s.args, lambda x, y: SubTermPosition(x, y), n+1)
   s.args = aux[0]
   return [s,aux[1]]
  if s.constructor == "Up":
   s.pos = n
   aux = SubTermPosition(s.args, n+1)
   s.args = aux[0]
   return [s, aux[1]]
  if s.constructor == "Ln":
    s.pos = n
    aux = SubTermPosition(s.args, n+1)
    s.args = aux[0]
    return [s, aux[1]]

  if s.constructor == "La":
   s.pos = n
   aux =  Passing(s.args, lambda x, y: SubTermPosition(x,y), n+1)
   s.args = aux[0]
   return [s, aux[1]]

  if s.constructor == "Lq":
    s.pos = n
    aux = SubTermPosition(s.args, n+1)
    s.args = aux[0]
    return [s, aux[1]]

def addPosition(s):
 aux = SubTermPosition(s,0)
 return aux[0]

def addValency(s):
 if type(s).__name__ == "PrimitiveTerm":
  return s
 if type(s).__name__ == "ConstructedTerm":
  if s.constructor in ["Pi", "La"]:
    v = valency(s)
    aux = [addValency(x) for x in s.args]
    s.args = aux
    s.valency = v
    return s
  else:
    aux = addValency(s.args)
    v = valency(s)
    s.args = aux
    s.valency = v
    return s


def niceset(s):
 aux = [str(n) for n in s]
 return "{"+ ','.join(aux)+"}"

def display(s):
 if type(s).__name__ == "PrimitiveTerm":
  return s.name
 if type(s).__name__ == "ConstructedTerm":
  if s.constructor in ["Pi", "La"]:
    aux =  ','.join([str(x) for x in s.param])
    return s.constructor + "(" + aux + ") " + ' '.join([display(x) for x in s.args])
  if s. constructor =="Up":
    aux = ''.join([niceset(x) for x in s.param[1]])
    return s.constructor  + aux + " " + display(s.args)
  else:
    return s.constructor  + " " + str(s.param) + " " + display(s.args)


def subterms(s):
 w = SubTermPosition(s,0)[0] 
 aux = subTerms2(w)
 for t in aux:
  if type(t).__name__!="PrimitiveTerm": 
   print(display(t) + " => " + str(t.pos))
 return

 
def substitution(ast,newsubt,pos):
 if ast.pos == pos:
  return newsubt
 if type(ast).__name__ == "PrimitiveTerm":
  return ast
 if type(ast).__name__ == "ConstructedTerm":
   if ast.constructor in ["Pi", "La"]:
    aux = [substitution(x,newsubt,pos) for x in ast.args]
    ast.args = aux
    
    return ast
   else:
    aux = substitution(ast.args,newsubt,pos)
    ast.args = aux
    return ast

def getSubterm(ast,pos):
 if ast.pos == pos:
  return ast
 if type(ast).__name__ == "PrimitiveTerm":
  return None
 if type(ast).__name__ == "ConstructedTerm":
   if ast.constructor in ["Pi", "La"]:
    aux = [getSubterm(x,pos) for x in ast.args if getSubterm(x,pos)!=None]
    if len(aux) > 0:
     return aux[0]
    else:
     return None
   else:
    return getSubterm(ast.args,pos)

def displayPos(s):
 p = "*"+str(s.pos)+"*"
 if type(s).__name__ == "PrimitiveTerm":
  return p + s.name
 if type(s).__name__ == "ConstructedTerm":
  if s.constructor in ["Pi", "La"]:
    aux =  ','.join([str(x) for x in s.param])
    return p + s.constructor + " (" + aux + ") " + ' '.join([displayPos(x) for x in s.args])
  if s. constructor =="Up":
    aux = ' '.join([str(x) for x in s.param[1]])
    return p + s.constructor + " " + aux + " " + displayPos(s.args)
  else:
    return p + s.constructor + " " + str(s.param) + " " + displayPos(s.args)


 


