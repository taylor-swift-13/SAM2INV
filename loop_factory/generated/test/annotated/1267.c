int main1(){
  int iiy, fsy, ka, t, b6v, g;
  iiy=1+14;
  fsy=0;
  ka=fsy;
  t=-3;
  b6v=1;
  g=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ka == 0) ==> (t == -3 && b6v == 1 && g == 0);
  loop invariant iiy == 1 + 14;
  loop invariant g >= 0;
  loop invariant g % 2 == 0;
  loop invariant (0 <= ka);
  loop invariant (ka <= iiy + 1);
  loop invariant (((ka == 0) ==> (t == -3)) && ((ka > 0) ==> (t == 0))) &&
                 (((ka == 0) ==> (b6v == 1)) && ((ka > 0) ==> (b6v == 0)));
  loop assigns t, b6v, g, ka;
*/
while (ka<=iiy) {
      t = t*ka;
      if (ka<iiy) {
          b6v = b6v*ka;
      }
      g = g*2+(b6v%4)+2;
      ka = ka + 1;
  }
}