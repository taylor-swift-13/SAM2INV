int main1(){
  int hi, fk, kky, vo, f;
  hi=1+6;
  fk=hi;
  kky=hi;
  vo=0;
  f=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (kky - (fk * (fk + 1) / 2) == (hi - (hi * (hi + 1) / 2)));
  loop invariant (f == (vo * (fk - hi)));
  loop invariant (fk <= hi);
  loop invariant f == 0;
  loop invariant kky - (fk * (fk + 1)) / 2 == -21;
  loop invariant hi == 7;
  loop invariant kky - fk*(fk+1)/2 == hi - hi*(hi+1)/2;
  loop invariant f == vo * (fk - hi);
  loop invariant fk <= hi;
  loop invariant 2*kky == fk*fk + fk - hi*(hi - 1);
  loop invariant (2 * kky - (fk * (fk + 1))) == (hi * (1 - hi));
  loop invariant f == (vo * (fk - hi));
  loop assigns fk, f, kky;
*/
while (fk < hi) {
      fk += 1;
      f = f + vo;
      kky = kky + fk;
  }
}