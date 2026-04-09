int main1(int e){
  int a, f, a2, g4t, sph;
  a=e*5;
  f=0;
  a2=-1;
  g4t=1;
  sph=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= f;
  loop invariant (a >= 0 ==> f <= a);
  loop invariant sph == (f * (f + 1 - a));
  loop invariant a2 == (-1 + f * g4t);
  loop invariant e == (\at(e, Pre) + (f * (f + 1) * (2 * f + 4 - 3 * a)) / 6);
  loop invariant a == (\at(e, Pre) * 5);
  loop invariant g4t == 1;
  loop invariant 6 * (e - \at(e, Pre)) == f * (f + 1) * (2 * f + 4 - 3 * a);
  loop assigns f, sph, e, a2;
*/
while (f < a) {
      f = f + 1;
      sph = sph + (f - (a - f));
      e = e + sph;
      a2 = a2 + g4t;
  }
}