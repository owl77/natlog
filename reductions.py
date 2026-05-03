import ntl
import weavers
import copy


print()
print("NTL term reduction assistant")
print()
print("2026 Clarence Lewis Protin")
print()
print("Commands: ShowPrimitive, AddPrimitives, StartTerm, S, Red, T, Reset")
print()

def disp(s):
 
 return ntl.display(s)



def checkUpId(ast):
      
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Up":
  return False
 return weavers.weaverEquals(ast.param, weavers.weaverIdentity(ast.param[0]))

def UpId(ast):
 if not checkUpId(ast):
   return ast
 return ast.args

def UpIdRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkUpId(aux):
    return None
 else:
   aux2 = UpId(aux)
   return ntl.substitution(ast,aux2,pos)



def checkCUp(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Up":
  return False
 aux = ast.args
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="Up":
   return False
 return True


def CUp(ast):
 if not checkCUp(ast):
   return ast
 w2 = ast.param
 w1 = ast.args.param
 w = weavers.weaverComp(w2,w1)
 aux = ast.args.args
 aux2 = ntl.ConstructedTerm("Up",w,aux)
 return aux2

def CUpRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkCUp(aux):
    return None
 else:
   aux2 = CUp(aux)
   return ntl.substitution(ast,aux2,pos)

def checkRPi(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Pi":
  return False
 aux = ast.args[0]
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="Pi":
   return False
 return True

#listPot does not work with objects which must have different positions so we need

def listPotPrimitive(name, val ,n):
 if not type(n) == int:
   return None
 if  n < 0:
  return None
 if n == 0:
   return []
 if n == 1:
  return [ntl.PrimitiveTerm(name,val)]
 else:
  return [ntl.PrimitiveTerm(name,val)] + listPotPrimitive(name,val, n-1)


def RPi(ast):
 if not checkRPi(ast):
   return ast
 t = ast.param
 t2 = [ntl.valency(x) for x in ast.args[1:]]
 s = ast.args[0].param
 s2 = [ntl.valency(x) for x in ast.args[0].args[1:]]

 a = weavers.associator([s2,s], [t2,t])
 S = ast.args[1:]
 T = ast.args[0].args[1:]
 aux = weavers.listDiv(S,s)
 r = weavers.remainderSelector([s2,s])
 aux2 = []
 for i in range(0, len(s)):
  aux2 = aux2 + [aux[i] + listPotPrimitive("I",1, r[i])]
 aux3 = []
 for i in range(0,len(s)):
  aux3 = aux3 + [ntl.ConstructedTerm("Pi", a[1][i][1], [T[i]] + aux2[i])]
 return ntl.ConstructedTerm("Pi", a[0][1], [ast.args[0].args[0]] + aux3)

def RPiRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkRPi(aux):
    return None
 else:
   aux2 = RPi(aux)
   return ntl.substitution(ast,aux2,pos)


def checkRUp(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Pi":
  return False
 aux = ast.args[0]
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="Up":
   return False
 return True

def RUp(ast):
 if not checkRUp(ast):
  return ast
 s = ast.param
 s2 = [ntl.valency(x) for x in ast.args[1:]]
 t = ast.args[0]
 S = ast.args[1:]
 w = t.param
 aux = weavers.oDot(w,s)
 n = len(aux[0])
 aux1 = weavers.weaverShift(aux, list(range(1,n+1)))
 aux2 = weavers.weaverSharpShift(w,s2)
 aux3 = weavers.weaverSharpShift(w,s)
 aux4 = weavers.weaverSharpShift(w,S)
 return ntl.ConstructedTerm("Up", aux1, ntl.ConstructedTerm("Pi", aux3, [t.args] + aux4))

def RUpRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkRUp(aux):
    return None
 else:
   aux2 = RUp(aux)
   return ntl.substitution(ast,aux2,pos)

def checkRI(ast):
 if type(ast).__name__=="ConstructedTerm":
  if ast.constructor == "Pi":
    if len(ast.args) == 2 and type(ast.args[0]).__name__=="PrimitiveTerm":
     if ast.args[0].name =="I":
       return True
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Pi":
  return False
 aux = ast.args[1:]
 for t in aux:
  if type(t).__name__ == "PrimitiveTerm":
   if t.name!="I":
    return False
  if type(t).__name__ =="ConstructedTerm":
    return False
 return True


def RI(ast):
 if not checkRI(ast):
  return ast
 if ast.args[0].name =="I":
  return ast.args[1]
 return ast.args[0]

def RIRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkRI(aux):
    return None
 else:
   aux2 = RI(aux)
   return ntl.substitution(ast,aux2,pos)

def checkRLn(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Pi":
  return False
 aux = ast.args[0]
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="Ln":
   return False
 return True

def RLn(ast):
 if not checkRLn(ast):
   return ast
 t = ast.param
 n = ast.args[0].param
 S = ast.args[1:]
 T = ast.args[0].args
 
 return ntl.ConstructedTerm("Ln", weavers.sumList(t), ntl.ConstructedTerm("Pi", t, [T] + S ))

def RLnRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkRLn(aux):
    return None
 else:
   aux2 = RLn(aux)
   return ntl.substitution(ast,aux2,pos)


def checkRLa(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Pi":
  return False
 aux = ast.args[0]
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="La":
   return False
 return True

def RLa(ast):
 if not checkRLa(ast):
   return ast
 B = ast.param
 b = weavers.sumList(B) 
 n = ast.args[0].param[0]
 m = ast.args[0].param[1]
 T = ast.args[1:]
 S1 = ast.args[0].args[0]
 S2 = ast.args[0].args[1]
 Bl = weavers.listDiv(B,ast.args[0].param)
 Tl = weavers.listDiv(T,ast.args[0].param)
 return ntl.ConstructedTerm("La",[weavers.sumList(Bl[0]), weavers.sumList(Bl[1])],[ntl.ConstructedTerm("Pi", Bl[0], [S1] + Tl[0]  ), ntl.ConstructedTerm("Pi", Bl[1] , [S2] + Tl[1])  ] )

def RLaRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkRLa(aux):
    return None
 else:
   aux2 = RLa(aux)
   return ntl.substitution(ast,aux2,pos)


def checkRLq(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Pi":
  return False
 aux = ast.args[0]
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="Lq":
   return False
 return True

def RLq(ast):
 if not checkRLq(ast):
   return ast
 t = ast.param
 n = ast.args[0].param
 S = ast.args[1:]
 T = ast.args[0].args
 i = ntl.PrimitiveTerm("I",1)
 return ntl.ConstructedTerm("Lq", 1 + weavers.sumList(t), ntl.ConstructedTerm("Pi", [1] + t, [T] + [i] + S  ))

def RLqRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkRLq(aux):
    return None
 else:
   aux2 = RLq(aux)
   return ntl.substitution(ast,aux2,pos)


def checkPPi(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Up":
  return False
 aux = ast.args
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="Pi":
   return False
 w = ast.param
 sel = ast.args.param
 sumsel = weavers.sumList(sel)
 seq = list(range(1, sumsel+1))
 part = weavers.listDiv(seq, sel)
 if weavers.weaverOut(w, part):
  return False
 return True


def PPi(ast):
 if not checkPPi(ast):
  return ast
 w = ast.param
 sel = ast.args.param
 t = ast.args.args[0]
 slist = ast.args.args[1:]
 n = len(slist)
 sel2 = [ntl.valency(x) for x in slist]
 d = weavers.remainderSelector([sel2,sel])
 sumsel = weavers.sumList(sel)
 seq = list(range(1, sumsel+1))
 part = weavers.listDiv(seq, sel)
 shifting = [list(range(1, sel[i]+1)) for i in range(0, len(sel))]
 restricts = weavers.factorInRestrictions(w, part)
 reslist = [weavers.weaverShift(restricts[i], shifting[i]) for i in range(0,n)]
 out = weavers.factorOut(w, part)
 In = weavers.factorIn(w,part)
 out2 = weavers.weaverShift(out, list(range(1, len(In[1]) +1)))
 rangesizes = [len(x[1]) for x in reslist]
 extras = [list(range( sel[i] +1, sel[i] + 1 + d[i]) ) for i in range(0,n)]
 weaverextras = [weavers.weaverIdentity(u) for u in extras]
 weaversnew = [weavers.weaverSum([reslist[i], weaverextras[i]]) for i in range(0, n)]
 aux = ntl.ConstructedTerm("Pi", rangesizes, [t] + [ntl.ConstructedTerm("Up", weaversnew[i], slist[i]) for i in range(0, n)])
 return ntl.ConstructedTerm("Up", out2, aux)

def PPiRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkPPi(aux):
    return None
 else:
   aux2 = PPi(aux)
   return ntl.substitution(ast,aux2,pos)


def checkPLa(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Up":
  return False
 aux = ast.args
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="La":
   return False
 w = ast.param
 nm = ast.args.param
 part = weavers.listDiv(w[0],nm)
 if weavers.weaverOut(w,part):
  return False
 return True

def PLa(ast):
 if not checkPLa(ast):
  return ast
 w = ast.param
 nm = ast.args.param
 n = nm[0]
 m = nm[1]
 s = ast.args.args[0]
 t = ast.args.args[1]
 part = weavers.listDiv(w[0],nm)
 restricts = weavers.factorInRestrictions(w, part)
 out = weavers.factorOut(w, part)
 w1 = restricts[0]
 w2 = weavers.weaverShift(restricts[1], list(range(1, m+1)))
 o = len(w1[1])
 p = len(w2[1])
 out2 = weavers.weaverShift(out, list(range(1, o + p + 1)))
 aux = ntl.ConstructedTerm("La", [o,p], [ntl.ConstructedTerm("Up", w1, s), ntl.ConstructedTerm("Up", w2, t)])
 return ntl.ConstructedTerm("Up", out2, aux)

def PLaRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkPLa(aux):
    return None
 else:
   aux2 = PLa(aux)
   return ntl.substitution(ast,aux2,pos)


def checkPLn(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Up":
  return False
 aux = ast.args
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="Ln":
   return False
 return True

def PLn(ast):
 if not checkPLn(ast):
  return ast
 w = ast.param
 t = ast.args.args
 m = len(w[1])
 return ntl.ConstructedTerm("Ln",m, ntl.ConstructedTerm("Up", w, t))

def PLnRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkPLn(aux):
    return None
 else:
   aux2 = PLn(aux)
   return ntl.substitution(ast,aux2,pos)

def checkPLq(ast):
 if type(ast).__name__ == "PrimitiveTerm":
  return False
 if ast.constructor!="Up":
  return False
 aux = ast.args
 if type(aux).__name__ == "PrimitiveTerm":
   return False
 if aux.constructor!="Lq":
   return False
 return True

def PLq(ast):
 if not checkPLq(ast):
  return ast
 w = ast.param
 t = ast.args.args
 m = len(w[1])
 w2 = weavers.weaverSum([ [["a"],[{"a"}]] , w])
 w3 = weavers.weaverShift(w2, list(range(1, len(w[0])+2)))
 return ntl.ConstructedTerm("Lq",m + 1, ntl.ConstructedTerm("Up", w3, t))

def PLqRed(ast,pos):
 aux = ntl.getSubterm(ast,pos)
 if not checkPLq(aux):
    return None
 else:
   aux2 = PLq(aux)
   return ntl.substitution(ast,aux2,pos)




#add more later

#interface

term = None

def AddPrimitive(name,val):
 if "name"!="I" and not name in ntl.Primitives.keys():
  ntl.Primitives[name] = val
 else:
  print("Name already taken or attempting to use I reserved for the unit primitive term.")
  return
 aux = [k + ":"+ str(ntl.Primitives[k]) for k in ntl.Primitives.keys()]
 print ("Primitives:  " + '  '.join(aux))
 return

def ShowPrimitives():
 aux = [k + ":"+ str(ntl.Primitives[k]) for k in ntl.Primitives.keys()]
 print ("Primitives:  " + '  '.join(aux))
 return



def T():
  print("Term: " + disp(term))
  return


def StartTerm(s):
 aux = ntl.Term(s)
 if aux!=None:
  global term
  term = aux
  print("Term: " + disp(term))
  return

def Reset():
 global term
 term = None
 return

def S():
 global term
 print ("Reducible subterms of: " + disp(term))
 print()
 w = ntl.SubTermPosition(term,0)[0] 
 aux = ntl.subTerms2(w)
 for t in aux:
  if type(t).__name__!="PrimitiveTerm":
   red = []
   if checkCUp(t):
     red = red + [" CUp "]
   
   if checkRPi(t):
     red = red + [" RPi "]
   if checkRUp(t): 
     red = red + [" RUp "]
   if checkRI(t):
     red = red + [" RI "]
   if checkRLn(t): 
     red = red + [" Ln "]
   if checkRLa(t): 
     red = red + [" La "]
   if checkRLq(t): 
     red = red + [" Lq "]
   if checkPPi(t): 
     red = red + [" PPi "]
   if checkPLa(t): 
     red = red + [" PLa "]
   if checkUpId(t): 
     red = red + [" UpId "]
   if checkPLn(t): 
     red = red + [" PLn "]
   if checkPLq(t): 
     red = red + [" PLq "]




   if len(red) > 0:
    print(disp(t) + " => " + str(t.pos) + "  " + ''.join(red))
 return

def Red(red, p):
 global term
 if red =="CUp":
   aux = CUpRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return
 if red =="RPi":
   aux = RPiRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return

 if red =="RUp":
   aux = RUpRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return
 if red =="RI":
   aux = RIRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return

 if red =="Ln":
   aux = RLnRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return

 if red =="La":
   aux = RLaRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return
 if red =="Lq":
   aux = RLqRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return

 if red =="PPi":
   aux = PPiRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return
 
 if red =="PLa":
   aux = PLaRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return
  
 if red =="PLn":
   aux = PLnRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return
 
 if red =="PLq":
   aux = PLqRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return

 if red =="UpId":
   aux = UpIdRed(term,p)
   if aux!=None:
    term = aux 
    S()
    return


    