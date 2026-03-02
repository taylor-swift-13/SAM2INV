int main1(int k,int p){
  int j, u, e, f;

  j=32;
  u=0;
  e=u;
  f=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == e * e && e >= 0;
  loop invariant k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant f == e * e;
  loop invariant e >= 0;
  loop invariant j == 32;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant f >= 0;
  loop invariant f == e*e;
  loop assigns e, f;
*/
while (1) {
      f = f+e;
      e = e+1;
      f = f+e;
  }

}
