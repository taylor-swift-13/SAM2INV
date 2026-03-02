int main1(int p,int q){
  int x, c, v;

  x=p;
  c=0;
  v=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant x == p;
  loop invariant p == \at(p, Pre) && q == \at(q, Pre);
  loop invariant v >= x;
  loop invariant v >= \at(p,Pre);
  loop invariant x == \at(p,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant q == \at(q,Pre);
  loop assigns v;
*/
while (1) {
      v = v+2;
      v = v*v;
  }

}
