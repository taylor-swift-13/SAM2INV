int main1(int p,int q){
  int h, z, v, f;

  h=73;
  z=3;
  v=-4;
  f=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (f == 2 && v == -4) || v == f*f;
  loop invariant f >= 2;
  loop invariant h == 73;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v == -4 || v == f*f;
  loop invariant p == \at(p, Pre) && q == \at(q, Pre);
  loop invariant (f == 2 && v == -4) || (f >= 3 && v == f*f);
  loop invariant v >= -4;
  loop invariant (v == f*f) || (f == 2 && v == -4);
  loop invariant v <= f * f;
  loop invariant v == f*f || (f == 2 && v == -4);
  loop assigns f, v;
*/
while (1) {
      f = f+1;
      v = f*f;
  }

}
