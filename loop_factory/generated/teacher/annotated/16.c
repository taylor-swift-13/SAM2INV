int main1(int p,int q){
  int u, e, y;

  u=67;
  e=0;
  y=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant u == 67;
  loop invariant e <= u;
  loop invariant ((e == 0) ==> (y == p)) && ((e > 0) ==> (y == 0));
  loop invariant 0 <= e;
  loop invariant (e > 0) ==> (y == 0);
  loop invariant (e == 0) ==> (y == p);
  loop invariant (e == 0 ==> y == \at(p, Pre)) && (e >= 1 ==> y == 0);
  loop invariant e >= 0;
  loop invariant (e == 0 ==> y == \at(p, Pre)) && (e > 0 ==> y == 0) && 0 <= e && e <= u;
  loop assigns e, y;
*/
while (e<u) {
      y = y-y;
      y = y+y;
      e = e+1;
  }

}
