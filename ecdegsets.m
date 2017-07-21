/*
    Magma code related to the paper:
    [1] "Cartan images and l-torsion points of elliptic curves with rational
        j-invariant."
    Copyright (c) 2017 by Oron Y. Propp.
    You are welcome to use and/or modify this code under the terms of version 3
    of the GNU General Public License or any later version (but please cite the
    paper if you use this code in your research).

    This module implements functions from [1], in particular ones computing the
    sets appearing in each table. Notation generally follows that used in the
    paper, and specific references are given throughout in the comments.

    This code depends on the following modules by Andrew V. Sutherland, which
    can be downloaded from:
        http://math.mit.edu/~drew/galrep/
    They are related to his paper:
    [2] "Computing images of Galois representations attached to elliptic
        curves," Forum of Mathematics, Sigma 4 (2016) e4 (79 pages),
        http://dx.doi.org/10.1017/fms.2015.33.
*/

load "subgroups.m";
load "distinguish.m";

// File containing (newline-separated) list of Sutherland's conjectured 63
// exceptional subgroups from [1, Table 1] or [2, Tables 3,4].
EXCEPTIONAL:="exceptional.txt";

// Subgroups of the Borel group defined in [1, Section 3].
G:=function(p)
    g:=PrimitiveRoot(p);
    return sub<GL(2,p)|[[1,0,0,-1],[g,0,0,g],[1,1,0,1]]>;
end function;

H1:=function(p)
    g:=PrimitiveRoot(p)^2;
    return sub<GL(2,p)|[[1,0,0,-1],[g,0,0,g],[1,1,0,1]]>;
end function;

H2:=function(p)
    g:=PrimitiveRoot(p)^2;
    return sub<GL(2,p)|[[-1,0,0,1],[g,0,0,g],[1,1,0,1]]>;
end function;

A:=function(p)
    g:=PrimitiveRoot(p);
    return sub<GL(2,p)|[[g,0,0,g],[1,1,0,1]]>;
end function;

// Functions defined in [1, Section 3].
Delta:=func<min,max|&join[{d*a:d in Divisors(ExactQuotient(b,a))}:
                          a in min,b in max|IsDivisibleBy(b,a)]>;
Pi:=func<n|Seqset(PrimeBasis(n))>;
PiOdd:=func<n|Pi(n) diff {2}>;
// Select a or b if l is 1 or 3 modulo 4, respectively.
Mod4Select:=func<l,a,b|l mod 4 eq 1 select a else b>;

// Sets (or functions testing membership) defined in [1, Section 1].
H:={3,7,11,19,43,67,163};
P:=func<l|&and[LegendreSymbol(-D,l) eq 1:D in H join {4,8}]>;
Q:=func<l|&and[LegendreSymbol(-D,l) eq -1:D in H join {4,8}]>;

// Verifies a claim in [1, Section 3].
VerifyHLegendre:=func<|&and[{LegendreSymbol(-D,l):
                             D in H join {4,8}} eq {-1,0,1}:l in H]>;

// Sets listed in [1, Tables 2,3,4,9,10 and Section 3], named accordingly.
// Throughout, the ith element of each list corresponds to the set with
// subscript a standard subgroup M as follows:
// [1,2,3,4,5,6] <-> [Z,Cs,Cns,Ns,Nns,A].
// Thus, I(Excep(l);Cs(l)) is the function I_Excep(2,l), S_Nns^CM(l) is the
// function S_CM(4,l), etc.
I_Excep:=func<m,l|l eq 3 select [Delta({2},{12,16}),
                                 Delta({1},{6,8}),
                                 Delta({2},{4}),
                                 Delta({1},{4}),
                                 Delta({1},{6,8}),
                                 Delta({2},{4})][m]
                 else l eq 5 select [Delta({4},{80,96}),
                                     Delta({1},{40,48}) diff {3},
                                     Delta({2},{12,32}),
                                     Delta({1},{12}),
                                     Delta({1},{40,48}) diff {5},
                                     Delta({4},{16})][m]
                 else l eq 7 select [Delta({6,14,16},{72,96,252}),
                                     Delta({2,3,7},{36,48,84,126}),
                                     Delta({2},{18,24}),
                                     Delta({1},{18,24}),
                                     Delta({1},{36,48,126}),
                                     Delta({2},{26})][m]
                 else l eq 11 select [Delta({24,110},{220,240}),
                                      Delta({11,12},{44,110,120}),
                                      Delta({2},{60,80}),
                                      Delta({6},{60}),
                                      Delta({1},{110,120}) diff {11,22},
                                      Delta({10},{20})][m]
                 else l eq 13 select [Delta({24,52},{288,1872}),
                                      Delta({6,8,13},{96,144,624,936}),
                                      Delta({12},{36}),
                                      Delta({3,4},{36}),
                                      Delta({6,26},{144,936}),
                                      Delta({4},{144})][m]
                 else l eq 17 select [Delta({272},{1088}),
                                      Delta({17},{544}),
                                      {},
                                      {},
                                      Delta({136},{544}),
                                      Delta({16},{64})][m]
                 else l eq 37 select [Delta({1332},{15984}),
                                      Delta({37},{5328,7992}),
                                      {},
                                      {},
                                      Delta({666},{7992}),
                                      Delta({36},{432})][m]
                 else {}>;

I_GL2:=func<m,l|[Delta({l*(l+1)*(l-1)},{l*(l+1)*(l-1)^2}),
                 Delta({l*(l+1)},{ExactQuotient(l*(l+1)*(l-1)^2,q):
                                  q in Pi(l-1)}),
                 Delta({l*(l-1)},
                       {ExactQuotient(l*(l+1)*(l-1)^2,q):
                        q in PiOdd(l+1) join {2^(Valuation(l-1,2)+1)}}),
                 Delta({ExactQuotient(l*(l+1),2)},
                       {ExactQuotient(l*(l+1)*(l-1)^2,2*q):
                        q in PiOdd(l-1) join Mod4Select(l,{4},{2})}),
                Delta({ExactQuotient(l*(l-1),2)},
                      {ExactQuotient(l*(l+1)*(l-1)^2,2)}),
                Delta({l^2-1},{(l+1)*(l-1)^2})][m]>;

I_Ns:=func<m,l|[Delta({2*(l-1)},{2*(l-1)^2}),
                Delta({2},{ExactQuotient(2*(l-1)^2,q):q in Pi(l-1)}),
                Delta({l-1},{ExactQuotient((l-1)^2,2^Valuation(l-1,2))}),
                Delta({1},{ExactQuotient((l-1)^2,q):
                           q in PiOdd(l-1) join Mod4Select(l,{4},{2})}),
                Delta({ExactQuotient(l-1,2)},{(l-1)^2}),
                {}][m]>;

I_Nns:=func<m,l|[Delta({2*(l+1)},{2*(l^2-1)}),
                 Delta({l+1},{l^2-1}),
                 Delta({2},{ExactQuotient(2*(l^2-1),q):
                            q in PiOdd(l+1) join {2^(Valuation(l-1,2)+1)}}),
                 Delta({ExactQuotient(l+1,2)},
                       {ExactQuotient(l^2-1,2^Valuation(l-1,2))}),
                 Delta({1},{l^2-1}),
                 {}][m]>;

I_G_H1_H2:=func<m,l|[Delta({2*l},{2*l*(l-1)}),
                     Delta({l},{l*(l-1)}),
                     {},
                     {},
                     Delta({l},{l*(l-1)}),
                     Delta({2},{2*(l-1)})][m]>;

E_CM:=func<m,l|P(l) select I_Ns(m,l)
               else Q(l) select I_Nns(m,l)
               else l in H select I_Ns(m,l) join I_Nns(m,l) join I_G_H1_H2(m,l)
               else I_Ns(m,l) join I_Nns(m,l)>;
E_nonCM:=func<m,l|I_Excep(m,l) join I_GL2(m,l)>;
E:=func<m,l|E_CM(m,l) join E_nonCM(m,l)>;

S:=func<m,l|l eq 3 select [{2},{1},{2},{1},{1}][m]
            else l eq 5 select [{4},{1},{2},{1},{1}][m]
            else l eq 7 select [{6,14,16},{2,3,7},{2},{1},{1}][m]
            else l eq 13 select [{24,28,52},{2,13},{2},{1},{1}][m]
            else l eq 17 select [{32,36,272},{2,17},{2},{1},{1}][m]
            else l eq 37 select [{72,76,1332},{2,37},{2},{1},{1}][m]
            else l in {11,19,43,67,163} select [{2*(l-1),2*l,2*(l+1)},{2,l},{2},
                                                {1},{1}][m]
            else P(l) select [{2*(l-1)},{2},{l-1},{1},{ExactQuotient(l-1,2)}][m]
            else Q(l) select [{2*(l+1)},{l+1},{2},{ExactQuotient(l+1,2)},{1}][m]
            else [{2*(l-1),2*(l+1)},{2},{2},{1},{1}][m]>;
S_CM:=func<m,l|l in H select [{2*(l-1),2*l,2*(l+1)},{2,l},{2},{1},{1}][m]
               else P(l) select [{2*(l-1)},{2},{l-1},{1},
                                 {ExactQuotient(l-1,2)}][m]
               else Q(l) select [{2*(l+1)},{l+1},{2},{ExactQuotient(l+1,2)},
                                 {1}][m]
               else [{2*(l-1),2*(l+1)},{2},{2},{1},{1}][m]>;
S_nonCM:=func<m,l|l eq 3 select [{2},{1},{2},{1},{1}][m]
                  else l eq 5 select [{4},{1},{2},{1},{1}][m]
                  else l eq 7 select [{6,14,16},{2,3,7},{2},{1},{1}][m]
                  else l eq 11 select [{24,110},{11,12},{2},{6},{1}][m]
                  else l eq 13 select [{24,52},{6,8,13},{12},{3,4},{6,26}][m]
                  else l eq 17 select [{272},{17},{272},{153},{136}][m]
                  else l eq 37 select [{1332},{37},{1332},{703},{666}][m]
                  else [{l*(l+1)*(l-1)},{l*(l+1)},{l*(l-1)},
                        {ExactQuotient(l*(l+1),2)},
                        {ExactQuotient(l*(l-1),2)}][m]>;

// Sets associated to [1, Thm. 1.3], defined in [1, (3.5)], and named
// accordingly.
K:=func<l|E(1,l) join E(2,l) join E(3,l) join E(6,l)>;
K_CM:=func<l|E_CM(1,l) join E_CM(2,l) join E_CM(3,l) join E_CM(6,l)>;
K_nonCM:=func<l|E_nonCM(1,l) join E_nonCM(2,l) join E_nonCM(3,l)
                join E_nonCM(6,l)>;

// Computes Table 5 as a list, given upper bounds L and D for primes and
// degrees, respectively.
AbExtTable:=func<L,D|[[d in K(l):d in [1..D]]:l in PrimesInInterval(3,L)]>;

// Sets listed in [1, Tables 6,7,11,12], named accordingly (note that Ij
// corresponds to I in the paper, and so forth).
Ij_Excep:=func<l|l in {2,3,5,7} select {1}
                  else l eq 11 select {5}
                  else l eq 13 select {2,3}
                  else l eq 17 select {4}
                  else l eq 37 select {6}
                  else {}>;
IQ_Excep:=func<l|l in {2,3,5,7} select {1}
                  else l eq 11 select {5}
                  else l eq 13 select {3,4}
                  else l eq 17 select {8}
                  else l eq 37 select {12}
                  else {}>;
Ij_GL2:=func<l|{ExactQuotient(l^2-1,2)}>;
IQ_GL2:=func<l|{l^2-1}>;
Ij_Ns:=func<l|{l-1}>;
IQ_Ns:=func<l|{2*(l-1)}>;
Ij_Nns:=func<l|{ExactQuotient(l^2-1,2)}>;
IQ_Nns:=func<l|{l^2-1}>;
Ij_G_H1_H2:=func<l|{ExactQuotient(l-1,2)}>;
IQ_G_H1_H2:=func<l|{ExactQuotient(l-1,2)}>;

T:=func<l|l in {3,5,7} select {1}
          else l eq 11 select {5}
          else l eq 13 select {2,3}
          else l eq 17 select {4}
          else l eq 37 select {6}
          else l in H select {ExactQuotient(l-1,2)}
          else Q(l) select {ExactQuotient(l^2-1,2)}
          else {l-1}>;
T_CM:=func<l|l in H select {ExactQuotient(l-1,2)}
             else Q(l) select {ExactQuotient(l^2-1,2)}
             else {l-1}>;
T_nonCM:=func<l|l in {3,5,7} select {1}
                else l eq 11 select {5}
                else l eq 13 select {2,3}
                else l eq 17 select {4}
                else l eq 37 select {6}
                else {ExactQuotient(l^2-1,2)}>;

TQ:=func<l|l in {3,5,7} select {1}
          else l eq 11 select {5}
          else l eq 13 select {3,4}
          else l eq 17 select {8}
          else l eq 37 select {12}
          else l in H select {ExactQuotient(l-1,2)}
          else Q(l) select {l^2-1}
          else {2*(l-1)}>;
TQ_CM:=func<l|l in H select {ExactQuotient(l-1,2)}
            else Q(l) select {ExactQuotient(l^2-1,2)}
            else {2*(l-1)}>;
TQ_nonCM:=func<l|l in {3,5,7} select {1}
               else l eq 11 select {5}
               else l eq 13 select {3,4}
               else l eq 17 select {8}
               else l eq 37 select {12}
               else {l^2-1}>;

// Computes the first column of [1, Table 8], for a prime l = 3 mod 4.
CMTorsDeg:=function(l)
    assert l mod 4 eq 3;
    return ClassNumber(-l)*ExactQuotient(l-1,2);
end function;

// The standard subgroup inclusion lattice in [1, (1,2)] (and [1, Section 3]).
InclStandSub:=AssociativeArray();
InclStandSub["Ns"]:="Cs";
InclStandSub["Cs"]:="Z";
InclStandSub["Z"]:="";
InclStandSub["Nn"]:="Cn";
InclStandSub["Cn"]:="Z";
InclStandSub["A"]:="Z";

// Computes whether a subgroup G of GL(2,p) is conjugate to a subgroup of a
// standard subgroup m, where m can be "Z", "A", or any of the other strings in
// GroupLetters (see the modules related to [2]).
IsConjSub:=function(G,m)
    local S;
    assert m in {"Z","A"} or m in GroupLetters;
    if m eq "Z" then S:=Scalars(#BaseRing(G));
    elif m eq "A" then S:=A(#BaseRing(G));
    else S:=GL2SubgroupFromLabel(IntegerToString(#BaseRing(G)) cat m);
    end if;
    return GL2SubgroupContains(S,G);
end function;

// Checks if G belongs to m (as defined in [1, Section 1]), for a standard
// subgroup m (as a string, e.g. "Ns") and subgroup G of GL(2,p).
Belongs:=function(G,m)
    assert m in Keys(InclStandSub);
    if m eq "Z" then return IsScalar(G);
    else return IsConjSub(G,m) and not IsConjSub(G,InclStandSub[m]);
    end if;
end function;

// Computes the div-minimal elements of a set S, as defined in [1, Section 2].
divMinima:=func<S|{s:s in S|
                    IsEmpty({t:t in S|t ne s and IsDivisibleBy(s,t)})}>;
// Computes the div-maximal elements of a set S, as defined in [1, Section 2].
divMaxima:=func<S|{s:s in S|
                    IsEmpty({t:t in S|t ne s and IsDivisibleBy(t,s)})}>;

// Computes the function I(G;m) defined in [1, Section 3], with G and m as
// above.
SubBelongs:=func<G,m|{d:d in Divisors(#G)|
                  not IsEmpty({g`subgroup:g in Subgroups(G:IndexEqual:=d)|
                               Belongs(g`subgroup,m)})}>;

// Partition a list L into a list of lists based on the value of a function f.
PartByFunc:=func<L,f|[[l:l in L|f(l) eq v]:v in {f(l):l in L}]>;

// Check if a set S can be expressed using the Delta notation defined in
// [1, Section 3].
IsDeltaSet:=func<S|S eq Delta(divMinima(S),divMaxima(S))>;

// Computes the sets I(Excep(l);m(l)) (for m as above) based on the subgroups
// appearing in the list EXCEPTIONAL, and attempts to express them using the
// Delta notation. Returns a list of tuples containing l, E_m(l), its d-minimal
// elements, its d-maximal elements, and whether it can be expressed using the
// Delta notation, respectively. The optional argument p specifies a list of
// primes to which the characteristic is to be restricted.
Compute_I_Excep:=function(m:data:=EXCEPTIONAL,p:=[])
    local S,f,L;
    S:=Split(Read(data));
    f:=func<s|#BaseRing(GL2SubgroupFromLabel(s))>;
    if p eq [] then
        L:=[<f(l[1]),&join[SubBelongs(GL2SubgroupFromLabel(e),m):
                           e in l]>:l in PartByFunc(S,f)];
    else
        L:=[<f(l[1]),&join[SubBelongs(GL2SubgroupFromLabel(e),m):
                           e in l]>:l in PartByFunc(S,f)|f(l[1]) in p];
    end if;
    return [<l[1],l[2],divMinima(l[2]),divMaxima(l[2]),
             IsDeltaSet(l[2])>:l in L];
end function;

// Computes the function I(G) defined in [1, Section 4], with G as above.
SubTorsTwist:=func<G|&join[{Index(G,g`subgroup):H in GL2Twists(g`subgroup)|
                            GroupTorsionDegree(GL2SubgroupFromLabel(H)) eq 1}:
                           g in Subgroups(G)]>;
// Computes the function I_Q(G) defined in [1, Section 4], with G as above.
SubTors:=func<G|{Index(G,H`subgroup):H in Subgroups(G)|
                 GroupTorsionDegree(H`subgroup) eq 1}>;

// Computes the sets I(Excep(l)) based on the subgroups appearing in the list
// EXCEPTIONAL, with p as above.
Compute_Ij_Excep:=function(:data:=EXCEPTIONAL,p:=[])
    local S,f,L;
    S:=Split(Read(data));
    f:=func<s|#BaseRing(GL2SubgroupFromLabel(s))>;
    if p eq [] then
        L:=[<f(l[1]),&join[SubTorsTwist(GL2SubgroupFromLabel(e)):
                           e in l]>:l in PartByFunc(S,f)];
    else
        L:=[<f(l[1]),&join[SubTorsTwist(GL2SubgroupFromLabel(e)):
                           e in l]>:l in PartByFunc(S,f)|f(l[1]) in p];
    end if;
    return [<l[1],divMinima(l[2])>:l in L];
end function;

// Computes the sets E based on the subgroups appearing in the list EXCEPTIONAL,
// with p as above.
Compute_IQ_Excep:=function(:data:=EXCEPTIONAL,p:=[])
    local S,f,L;
    S:=Split(Read(data));
    f:=func<s|#BaseRing(GL2SubgroupFromLabel(s))>;
    if p eq [] then
        L:=[<f(l[1]),&join[SubTors(GL2SubgroupFromLabel(e)):
                           e in l]>:l in PartByFunc(S,f)];
    else
        L:=[<f(l[1]),&join[SubTors(GL2SubgroupFromLabel(e)):
                           e in l]>:l in PartByFunc(S,f)|f(l[1]) in p];
    end if;
    return [<l[1],divMinima(l[2])>:l in L];
end function;
