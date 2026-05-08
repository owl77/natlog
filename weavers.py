import copy

#operations on lists and sets

def uniqueList(l):
 if not type(l) == list:
         return False
 aux = []
 for x in l:
  if x in aux:
    return False
  aux = aux + [x]
 return True

def subList(lst1, lst2):
   ls1 = [element for element in lst1 if element in lst2]
   ls2 = [element for element in lst2 if element in lst1]
   return ls1 == ls2

def isListOfLists(l):
 if not type(l) == list:
   return False
 for x in l:
   if not type(x) == list:
     return False
 return True

def isListOfSets(l):
 if not type(l) == list:
   return False
 for x in l:
   if not type(x) == set:
     return False
 return True


def listUnion(l):
 if not isListOfLists(l):
  return None
 aux = []
 for x in l:
  aux = aux + x
 return aux

def setUnion(l):
 if not isListOfSets(l):
  return None
 aux = []
 for x in l:
  aux = aux + list(x)
 return set(aux)


def setListCont(a,b):
 if not type(a) == list or not type(b) ==  list:
  return False
 for x in a:
  if not x in b:
   return False
 return True

def setListEquals(a,b):
 if setListCont(a,b) and setListCont(b,a):
   return True
 return False

def setCont(a,b):
 if not type(a) == set or not type(b) ==  set:
  return False
 for x in a:
  if not x in b:
   return False
 return True

def setEquals(a,b):
 if setCont(a,b) and setCont(b,a):
   return True
 return False



def listIntersection(l1,l2):
 if type(l1)!= list or type(l2)!= list:
  return None
 return [x for x in l1 if x in l2] 

def setIntersection(l1,l2):
 if type(l1)!= set or type(l2)!= set:
  return None
 return set([x for x in l1 if x in l2]) 




def emptyIntersectionListOfLists(l):
 if not isListOfLists(l):
   return False
 if len(l) == 0 or len(l) == 1:
   return True
 a= l[0]
 for b in l[1:]:
  if len(listIntersection(a,b)) > 0:
   return False
 return emptyIntersectionListOfLists(l[1:])

def noEmptyListOfLists(l):
 if not isListOfLists(l):
  return False
 for a in l:
  if len(a)== 0:
   return False
 return True


def emptyIntersectionListOfSets(l):
 if not isListOfSets(l):
   return False
 if len(l) == 0 or len(l) == 1:
   return True
 a= l[0]
 for b in l[1:]:
  if len(setIntersection(a,b)) > 0:
   return False
 return emptyIntersectionListOfSets(l[1:])

def noEmptyListOfSets(l):
 if not isListOfSets(l):
  return False
 for a in l:
  if len(a)== 0:
   return False
 return True


def indexes(l,x):
 if not type(l) == list:
  return None
 aux = []
 for i in range(len(l)):
   if l[i] == x:
     aux = aux + [i]
 return aux


def isListOfSetsOfPosIntegers(l):
  if not isListOfSets(l):
   return False
  for s in l:
   for a in s:
    if not type(a) == int:
     return False
    if a < 0:
      return False
  return True

def getSetofORel(l):
  if not isListOfSetsOfPosIntegers(l):
   return None
  aux = []
  for s in l:
   for a in s:
    aux = aux + [a]
  if not setListEquals(list(range(1, len(aux)+1)), aux):
   return None
  return list(range(1,len(aux)+1))



#weaver theory

def isWeaver(w):
 if not type(w) == list:
   return False
 if not len(w) == 2:
   return False
 if not uniqueList(w[0]) or not isListOfSets(w[1]):
   return False
 if not setListEquals(w[0], list(setUnion(w[1]))) or not emptyIntersectionListOfSets(w[1]) or not noEmptyListOfSets(w[1]):
   return False
 return True

def weaverShift(w,a):
 if not isWeaver(w) or not uniqueList(a):
   return None
 if not len(w[0]) == len(a):
   return None
 key = {}
 for n in range(0,len(a)):
  if type(w[0][n]) == set:
    key[frozenset(list(w[0][n]))] = a[n]
  else:
   key[w[0][n]] = a[n]
 aux = []
 for r in w[1]:
  aux = aux + [set([key[x] for x in r])]
 return [a,aux]

def weaverComp(w2,w1):
 if not isWeaver(w2) or not isWeaver(w1):
   return None
 if not len(w1[1]) == len(w2[0]):
   return None
 f = [frozenset(x) for x in w1[1]]
 aux = weaverShift(w2, f)
 aux2 = []
 for a in aux[1]:
  aux2 = aux2 + [[set(b) for b in a]]
 aux3 = [setUnion(u) for u in aux2]
 return [w1[0], aux3]

def weaverSharp(w):
 if not isWeaver(w):
  return None
 aux = []
 for x in w[0]:
  for y in w[1]:
   if x in y:
    aux = aux + [y]
 return aux

def weaverSharpShift(w,a):
 if not isWeaver(w):
  return None
 if not len(w[1]) == len(a):
  return None
 aux = []
 for x in w[0]:
  for y in range(0,len(w[1])):
   if x in w[1][y]:
    aux = aux + [a[y]]
 return aux
 
def canonicalWeaver(x,s):
 if not uniqueList(s) or not type(s) == list:
  return None
 if not setListEquals(x,s):
  return None
 aux = []
 for y in s:
  aux = aux + [set(indexes(x,y))]
 return [list(range(0,len(x))), aux]

def weaverRestriction(w,a):
 if not isWeaver(w) or not uniqueList(a):
   return None
 if not setListCont(a,w[0]):
   return None
 aux2 = [setIntersection(x,set(a)) for x in w[1]]
 aux3 = [b for b in aux2 if len(b)> 0]
 return [a, aux3]

def weaverSum(c):
 if type(c)!=list:
   return None
 for w in c:
  if not type(w)==list:
    return None
 aux1 = [w[0] for w in c]
 aux2 = [w[1] for w in c]
 aux3 = listUnion(aux1)
 aux4 = listUnion(aux2)
 return [aux3,aux4]

def weaverEquals(w,v):
 if not isWeaver(w) or not isWeaver(v):
   return False
 if not len(w[0]) == len(v[0]) or not len(w[1])== len(v[1]):
   return False
 for n in range(0, len(w[0])):
  if w[0][n] != v[0][n]:
   return False
 for m in range(0, len(w[1])):
  if not setEquals(w[1][m], v[1][m]):
    return False
 return True


def weaverIdentity(a):
 if not uniqueList(a):
  return None
 aux = [set([s]) for s in a]
 return [a,aux]


def isSegment(l,s):
 if not type(l) == list:
   return False
 for i in range(0,len(l)):
  for j in range(0, len(l)):
    if not j < i and s == l[i:j+1]:
     return True
 return False

def isPartition(l,pp):
 if not uniqueList(l):
   return False
 if not type(pp) == list:
  return False
 p = []
 for t in pp:
   if t != []:
    p = p + [t]
 for x in p:
  if not isSegment(l,x):
   return False
 if not listUnion(p) == l:
   return False
 if len(p) < 2:
  return True
 if not p[0][0] == l[0]:
   return False
 
 for i in range(0,len(p)-1):
   aux = p[i][len(p[i]) -1]
   j = l.index(aux)
   if not p[i+1][0] == l[j]:
     False
 return True

def weaverIn(w,p):
 if not isWeaver(w):
  return False
 if not isPartition(w[0],p):
  return False
 l = [weaverRestriction(w,i) for i in p]
 return weaverEquals(w, weaverSum(l))

def inducedPartition(w,p):
 if not weaverIn(w,p):
  return False
 l = [weaverRestriction(w,i) for i in p]
 aux = []
 for v in l:
  aux = aux + [v[1]]
 return aux

def weaverOut(w,p):
 if not isWeaver(w):
  return False
 if not isPartition(w[0],p):
  return False
 l = [weaverRestriction(w,i) for i in p]
 for v in l:
  if not weaverEquals(weaverIdentity(v[0]), v):
   return False
 return True

def factorIn(w,p):
 if not isWeaver(w):
  return False
 if not isPartition(w[0],p):
  return False
 l = [weaverRestriction(w,i) for i in p]
 return weaverSum(l)

def factorInRestrictions(w,p):
 if not isWeaver(w):
  return False
 if not isPartition(w[0],p):
  return False
 return [weaverRestriction(w,i) for i in p]
 


def factorOut(w,p):
 if not isWeaver(w):
  return False
 if not isPartition(w[0],p):
  return False
 i = factorIn(w,p)
 j = [frozenset(list(a)) for a in i[1]]
 aux = []
 for e in w[1]:
  aux = aux + [set([x for x in j if setCont(set(x),e)])]
 return [i[1], aux]
  

def isSelector(s):
 if not type(s) == list:
  return False
 if not len(s) == 2:
  return False
 if not type(s[0]) == list or not type(s[1]) == list:
  return False
 if not len(s[0]) == len(s[1]):
  return False
 for x in s[0]:
  if not type(x) == int:
   return False
 for x in s[1]:
  if not type(x) == int:
   return False
 for i in range(0,len(s[0])):
  if not s[1][i] <= s[0][i]:
   return False
 return True





def sumList(s):
 if not type(s) == list:
   return None
 for x in s:
  if not type(x) == int:
     return None
 if len(s) == 0: 
   return None
 if len(s) == 1:
  return s[0]
 return s[0] + sumList(s[1:len(s)])

def listPot(x,n):
 if not type(n) == int:
   return None
 if  n < 0:
  return None
 if n == 0:
   return []
 if n == 1:
  return [x]
 else:
  return [x] + listPot(x, n-1)


def listDiv(s,n):
 if not sumList(n) == len(s):
   return None
 if len(s) == 0:
   return s
 if len(n) == 1:
  return [s]
 else:
  return [s[0:n[0]]] + listDiv(s[n[0]:len(s)], n[1: len(n)])


def remainderSelector(s):
 if not isSelector(s):
  return None
 aux = []
 for i in range(0, len(s[0])):
  aux = aux + [s[0][i] - s[1][i]]
 return aux


def associator(s,t):
 if not isSelector(s) or not isSelector(t):
   return None
 if not len(t[0]) == sumList(s[1]):
   return None
 ms = listDiv(t[0], s[1])
 ts = listDiv(t[1], s[1])
 k = len(ms)
 r = remainderSelector(s)
 blist = []

 for i in range(0, k):
  blist = blist + [[ ms[i]+listPot(1,r[i]),  ts[i] + listPot(1,r[i]) ]]
 a1 = []
 a2 = []
 for j in range(0,k):
  a1 = a1 + [sumList(blist[j][1])]
  a2 = a2 + [sumList(ts[j])]
 a = [a1,a2]
 return [a,blist]


def squarePot(x,n):
 if type(n)!= int:
  return None
 if n < 0:
   return None
 if n == 0:
   return []
 return squarePot(x,n-1) + [(x,n)]

def squareListPot(l,n):
 if type(n)!= int or type(l)!=list:
  return None
 if n < 0:
   return None
 if n == 0:
   return []
 aux = []
 for i in range(0,n):
  aux = aux + [[(x,i+1) for x in l]]
 return aux

def squareSetPot(l,n):
 if type(n)!= int or type(l)!=set:
  return None
 if n < 0:
   return None
 if n == 0:
   return []
 aux = []
 for i in range(0,n):
  aux = aux + [set([(x,i+1) for x in l])]
 return aux



def listInsert(l,s,ind):
 if not type(l) == list or not type(s) == list:
  return None
 if not type(ind) == int:
  return None
 if ind < 0:
  return None
 if ind > len(l):
  return None
 return l[:ind] + s + l[ind+1:]



def oDot(w,l):
 if not isWeaver(w):
  return None
 if not type(l)== list:
   return None
 for s in l:
  if not type(s) == int:
   return None
 if not len(w[1]) == len(l):
   return None
 aux = []
 aux2 = copy.deepcopy(w[0])
 for i in range(0, len(l)):
  aux = aux + squareSetPot(w[1][i],l[i])
  for k in w[1][i]:
    j = indexes(aux2,k)[0]
    
    aux2 = listInsert(aux2, squarePot(aux2[j], l[i]),j)
 return [aux2, aux]


 
def sequenceToPartition(l,s):
 if not type(l).__name__ =="list"  or not type(s).__name__== "list":
  return None
 for i in range(0, len(s)):
  if not type(s[i]).__name__ =="int":
    return None
  if i < 0:
    return None
 if not sumList(s) == len(l):
   return None
 if len(s) == 0:
   return [[]]
 if len(s) == 1:
   return [l]
 return [l[0:s[0]]] + sequenceToPartition(l[s[0]:], s[1:])


   



    

 

 