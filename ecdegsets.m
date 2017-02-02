/*
    Magma code related to the paper:
    [1] "Cartan images and l-torsion points of elliptic curves with rational
        j-invariant," [https://arxiv.org/abs/1702.00121].
    Copyright (c) 2017 by Oron Y. Propp.
    You are welcome to use and/or modify this code under the terms of version 3
    of the GNU General Public License or any later version (but please cite the
    paper if you use this code in your research).

    This module implements functions from [1], in particular ones computing the
    sets appearing in each table. Notation generally follows that used in the
    paper, and specific references are given throughout in the comments.

    This code depends on the following modules by Andrew V. Sutherland, which
    can be downloaded from:
        [http://math.mit.edu/~drew/galrep/].
    They are related to his paper:
    [2] "Computing images of Galois representations attached to elliptic
        curves," Forum of Mathematics, Sigma 4 (2016) e4 (79 pages),
        [http://dx.doi.org/10.1017/fms.2015.33].
*/

load "subgroups.m";
load "distinguish.m";

// File containing (newline-separated) list of Sutherland's conjectured 63
// exceptional subgroups from [2, Tables 3,4].
EXCEPTIONAL:="exceptional.txt";

// Functions defined in [1, Section 3].
Delta:=func<min,max|&join[{d*a:d in Divisors(ExactQuotient(b,a))}:
                          a in min,b in max|IsDivisibleBy(b,a)]>;
Eta:=func<l|l*(l+1)*(l-1)^2>;
PhiOdd:=func<n|Seqset(PrimeBasis(n)) diff {2}>;
// Select a or b if l is 1 or 3 modulo 4, respectively.
Mod4Select:=func<l,a,b|l mod 4 eq 1 select a else b>;

// Sets (or functions testing membership) defined in [1, Section 1].
H:={3,7,11,19,43,67,163};
P:=func<l|&and[LegendreSymbol(-D,l) eq 1:D in H join {4,8}]>;
Q:=func<l|&and[LegendreSymbol(-D,l) eq -1:D in H join {4,8}]>;

// Verifies a claim in [1, Section 3].
VerifyHLegendre:=func<|&and[{LegendreSymbol(-D,l):
                             D in H join {4,8}} eq {-1,0,1}:l in H]>;

// Sets listed in [1, Tables 1,2,3,7,8 and Section 3], named accordingly.
// Throughout, the ith element of each list corresponds to the set with
// subscript a standard subgroup M as follows:
// [1,2,3,4] <-> [Cs,Cns,Ns,Nns].
// Thus, E_Cs(l) is the function EM[1], R_Nns^CM(l) is the function RCM[4], etc.
EM:=[func<l|l eq 3 select Delta({1},{2,3})
            else l eq 5 select Delta({1},{80,96}) diff {3}
            else l eq 7 select Delta({2,3,7},{72,96,252})
            else l eq 11 select Delta({11,12},{220,240})
            else l eq 13 select Delta({6,8,13},{288,1872})
            else l eq 17 select Delta({17},{1088})
            else l eq 37 select Delta({37},{15984})
            else {}>,
     func<l|l eq 3 select Delta({1},{1})
            else l eq 5 select Delta({2},{4})
            else l eq 7 select Delta({2},{12,32})
            else l eq 11 select Delta({2},{18,24})
            else l eq 13 select Delta({2},{60,80})
            else l eq 17 select {}
            else l eq 37 select {}
            else {}>,
     func<l|l eq 3 select Delta({1},{1})
            else l eq 5 select Delta({2},{4})
            else l eq 7 select Delta({2},{12,32})
            else l eq 11 select Delta({2},{18,24})
            else l eq 13 select Delta({2},{60,80})
            else l eq 17 select {}
            else l eq 37 select {}
            else {}>,
     func<l|l eq 3 select Delta({1},{2})
            else l eq 5 select Delta({1},{8})
            else l eq 7 select Delta({1},{12})
            else l eq 11 select Delta({1},{30,40})
            else l eq 13 select {}
            else l eq 17 select {}
            else l eq 37 select {}
            else {}>];

FM:=[func<l|Delta({l*(l+1)},{Eta(l)})>,
     func<l|Delta({l*(l-1)},
                  {ExactQuotient(Eta(l),q):
                   q in PhiOdd(l+1) join {2^(Valuation(l-1,2)+1)}})>,
     func<l|Delta({ExactQuotient(l*(l+1),2)},
                  {ExactQuotient(Eta(l),2*q):q in PhiOdd(l-1) join {4}})>,
     func<l|Delta({ExactQuotient(l*(l-1),2)},
                  {ExactQuotient(Eta(l),2*q):
                   q in PhiOdd(l+1) join Mod4Select(l,{},{4})})>];

SM:=[func<l|Delta({2},{2*(l-1)^2})>,
     func<l|Delta({l-1},{ExactQuotient((l-1)^2,2^Valuation(l-1,2))})>,
     func<l|Delta({1},{ExactQuotient((l-1)^2,q):q in PhiOdd(l-1) join {4}})>,
     func<l|{}>];

NM:=[func<l|Delta({l+1},{2*(l^2-1)})>,
     func<l|Delta({2},{ExactQuotient(2*(l^2-1),q):
                       q in PhiOdd(l+1) join {2^(Valuation(l-1,2)+1)}})>,
     func<l|Delta({ExactQuotient(l+1,2)},
                  {ExactQuotient(l^2-1,2^(Valuation(l-1,2)+1))})>,
     func<l|Delta({1},{ExactQuotient(l^2-1,q):
                       q in PhiOdd(l+1) join Mod4Select(l,{0},{4})})>];

BM:=[func<l|Delta({l},{2*l*(l-1)})>,
     func<l|{}>,
     func<l|{}>,
     func<l|{}>];

ZCM:=[func<l|P(l) select SM[i](l)
           else Q(l) select NM[i](l)
           else l in H select SM[i](l) join NM[i](l) join BM[i](l)
           else SM[i](l) join NM[i](l)>:i in [1..4]];
ZNonCM:=[func<l|EM[i](l) join FM[i](l)>:i in [1..4]];
Z:=[func<l|ZCM[i](l) join ZNonCM[i](l)>:i in [1..4]];

R:=[func<l|l in {3,5} select {1}
           else l eq 7 select {2,3,7}
           else l in H join {13,17,37} select {2,l}
           else P(l) select {2}
           else Q(l) select {l+1}
           else {2}>,
    func<l|l in {3,5} select {2}
           else l eq 7 select {2}
           else l in H join {13,17,37} select {2}
           else P(l) select {l-1}
           else Q(l) select {2}
           else {2}>,
    func<l|l in {3,5} select {1}
           else l eq 7 select {1}
           else l in H join {13,17,37} select {1}
           else P(l) select {1}
           else Q(l) select {ExactQuotient(l+1,2)}
           else {1}>,
    func<l|l in {3,5} select {1}
           else l eq 7 select {1}
           else l in H join {13,17,37} select {1}
           else P(l) select {}
           else Q(l) select {1}
           else {1}>];
RCM:=[func<l|l in H select {2,l}
             else P(l) select {2}
             else Q(l) select {l+1}
             else {2}>,
      func<l|l in H select {2}
             else P(l) select {l-1}
             else Q(l) select {2}
             else {2}>,
      func<l|l in H select {1}
             else P(l) select {1}
             else Q(l) select {ExactQuotient(l+1,2)}
             else {1}>,
      func<l|l in H select {1}
             else P(l) select {}
             else Q(l) select {1}
             else {1}>];
RNonCM:=[func<l|l in {3,5} select {1}
                else l eq 7 select {2,3,7}
                else l eq 11 select {11,12}
                else l eq 13 select {6,8,13}
                else l eq 17 select {17}
                else l eq 37 select {37}
                else {l*(l+1)}>,
         func<l|l in {3,5} select {2}
                else l eq 7 select {2}
                else l eq 11 select {2}
                else l eq 13 select {12}
                else l eq 17 select {272}
                else l eq 37 select {1332}
                else {l*(l-1)}>,
         func<l|l in {3,5} select {1}
                else l eq 7 select {1}
                else l eq 11 select {6}
                else l eq 13 select {3,4}
                else l eq 17 select {153}
                else l eq 37 select {703}
                else {ExactQuotient(l*(l+1),2)}>,
         func<l|l in {3,5} select {1}
                else l eq 7 select {1}
                else l eq 11 select {1}
                else l eq 13 select {78}
                else l eq 17 select {136}
                else l eq 37 select {666}
                else {ExactQuotient(l*(l-1),2)}>];

// Sets associated to [1, Thm. 1.3], defined in [1, (3.2)], and named
// accordingly.
V:=func<l|Z[1](l) join Z[2](l)>;
VCM:=func<l|ZCM[1](l) join ZCM[2](l)>;
VNonCM:=func<l|ZNonCM[1](l) join ZNonCM[2](l)>;

W:=func<l|Z[3](l) join Z[4](l)>;
WCM:=func<l|ZCM[3](l) join ZCM[4](l)>;
WNonCM:=func<l|ZNonCM[3](l) join ZNonCM[4](l)>;

// Computes Table 4 as a list, given upper bounds L and D for primes and
// degrees, respectively.
AbExtTable:=func<L,D|[[d in V(l):d in [1..D]]:l in PrimesInInterval(3,L)]>;

// Sets listed in [1, Tables 5,6,9,10], named accordingly.
E:=func<l|l in {2,3,5,7} select {1}
          else l eq 11 select {5}
          else l eq 13 select {3,4}
          else l eq 17 select {8}
          else l eq 37 select {12}
          else {}>;
Ej:=func<l|l in {2,3,5,7} select {1}
           else l eq 11 select {5}
           else l eq 13 select {2,3}
           else l eq 17 select {4}
           else l eq 37 select {6}
           else {}>;
F:=func<l|{l^2-1}>;
Fj:=func<l|{ExactQuotient(l^2-1,2)}>;
S:=func<l|{2*(l-1)}>;
Sj:=func<l|{l-1}>;
N:=func<l|{l^2-1}>;
Nj:=func<l|{ExactQuotient(l^2-1,2)}>;
B:=func<l|{ExactQuotient(l-1,2)}>;
Bj:=func<l|{ExactQuotient(l-1,2)}>;

T:=func<l|l in {3,5,7} select {1}
          else l eq 11 select {5}
          else l eq 13 select {3,4}
          else l eq 17 select {8}
          else l eq 37 select {12}
          else l in H select {ExactQuotient(l-1,2)}
          else Q(l) select {l^2-1}
          else {2*(l-1)}>;
TCM:=func<l|l in H select {ExactQuotient(l-1,2)}
            else Q(l) select {ExactQuotient(l^2-1,2)}
            else {2*(l-1)}>;
TNonCM:=func<l|l in {3,5,7} select {1}
               else l eq 11 select {5}
               else l eq 13 select {3,4}
               else l eq 17 select {8}
               else l eq 37 select {12}
               else {l^2-1}>;
Tj:=func<l|l in {3,5,7} select {1}
           else l eq 11 select {5}
           else l eq 13 select {2,3}
           else l eq 17 select {4}
           else l eq 37 select {6}
           else l in H select {ExactQuotient(l-1,2)}
           else Q(l) select {ExactQuotient(l^2-1,2)}
           else {l-1}>;
TjCM:=func<l|l in H select {ExactQuotient(l-1,2)}
             else Q(l) select {ExactQuotient(l^2-1,2)}
             else {l-1}>;
TjNonCM:=func<l|l in {3,5,7} select {1}
                else l eq 11 select {5}
                else l eq 13 select {2,3}
                else l eq 17 select {4}
                else l eq 37 select {6}
                else {ExactQuotient(l^2-1,2)}>;

// Computes the function M defined in [1, Section 2] for a subgroup G of
// GL(2,p).
M:=func<G|GroupLetters[GL2SubgroupID(G)[3]+1]>;
// Checks if M(G)=m for a standard subgroup m (as a string, e.g. "Ns") and
// subgroup G of GL(2,p).
MEq:=function(G,m)
    assert m in GroupLetters;
    return M(G) eq m;
end function;

// Computes the d-minimal elements of a set S, as defined in [1, Section 2].
dMinimalElts:=func<S|{s:s in S|
                      IsEmpty({t:t in S|t ne s and IsDivisibleBy(s,t)})}>;
// Computes the d-maximal elements of a set S, as defined in [1, Section 2].
dMaximalElts:=func<S|{s:s in S|
                      IsEmpty({t:t in S|t ne s and IsDivisibleBy(t,s)})}>;

// Computes the function I(G,M) defined in [1, Section 3], with G and m as
// above.
SubMEq:=func<G,m|{d:d in Divisors(#G)|
                  not IsEmpty({g`subgroup:g in Subgroups(G:IndexEqual:=d)|
                               MEq(g`subgroup,m)})}>;

// Partition a list L into a list of lists based on the value of a function f.
PartByFunc:=func<L,f|[[l:l in L|f(l) eq v]:v in {f(l):l in L}]>;

// Check if a set S can be expressed using the Delta notation defined in
// [1, Section 3].
IsDeltaSet:=func<S|S eq Delta(dMinimalElts(S),dMaximalElts(S))>;

// Computes the sets EM (for m as above) based on the subgroups appearing in the
// list EXCEPTIONAL, and attempts to express them using the Delta notation.
// Returns a list of tuples containing l, E_m(l), its d-minimal elements, its
// d-maximal elements, and whether it can be expressed using the Delta notation,
// respectively.
ComputeEM:=function(m:data:=EXCEPTIONAL)
    local S,f,P;
    S:=Split(Read(data));
    f:=func<s|#BaseRing(GL2SubgroupFromLabel(s))>;
    P:=[<f(p[1]),&join[SubMEq(GL2SubgroupFromLabel(e),m):
                       e in p]>:p in PartByFunc(S,f)];
    return [<p[1],p[2],dMinimalElts(p[2]),dMaximalElts(p[2]),
             IsDeltaSet(p[2])>:p in P];
end function;

// Computes the function I(G) defined in [1, Section 4], with G as above.
SubTors:=func<G|{Index(G,H`subgroup):H in Subgroups(G)|
                 GroupTorsionDegree(H`subgroup) eq 1}>;
// Computes the function I_j(G) defined in [1, Section 4], with G as above.
SubTorsTwist:=func<G|&join[{Index(G,g`subgroup):H in GL2Twists(g`subgroup)|
                            GroupTorsionDegree(GL2SubgroupFromLabel(H)) eq 1}:
                           g in Subgroups(G)]>;

// Computes the sets E based on the subgroups appearing in the list EXCEPTIONAL.
ComputeE:=function(:data:=EXCEPTIONAL)
    local S,f,P;
    S:=Split(Read(data));
    f:=func<s|#BaseRing(GL2SubgroupFromLabel(s))>;
    P:=[<f(p[1]),&join[SubTors(GL2SubgroupFromLabel(e)):
                       e in p]>:p in PartByFunc(S,f)];
    return [<p[1],dMinimalElts(p[2])>:p in P];
end function;

// Computes the sets E_j based on the subgroups appearing in the list
// EXCEPTIONAL.
ComputeEj:=function(:data:=EXCEPTIONAL)
    local S,f,P;
    S:=Split(Read(data));
    f:=func<s|#BaseRing(GL2SubgroupFromLabel(s))>;
    P:=[<f(p[1]),&join[SubTorsTwist(GL2SubgroupFromLabel(e)):
                       e in p]>:p in PartByFunc(S,f)];
    return [<p[1],dMinimalElts(p[2])>:p in P];
end function;
