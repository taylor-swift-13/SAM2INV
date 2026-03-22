int main1(int n,int b){
  int od, p6, na, si, e6;
  od=12;
  p6=0;
  na=0;
  si=0;
  e6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e6 == na;
  loop invariant (na == 0) ==> (si == 0);
  loop invariant (na > 0) ==> (si == na - 1);
  loop invariant si <= od - 1;
  loop invariant 0 <= e6 <= od;
  loop invariant 0 <= si <= od - 1;
  loop assigns e6, na, si;
*/
while (na<od) {
      if (e6<od) {
          si = na;
      }
      e6 += 1;
      na = na + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= p6 <= si;
  loop assigns na, od, p6;
*/
while (p6<si) {
      na = na+e6*p6;
      od += p6;
      p6 = si;
  }
}