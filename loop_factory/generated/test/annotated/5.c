int main1(){
  int gv, xz5, jzd;
  gv=1*5;
  xz5=-3;
  jzd=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gv == 5;
  loop invariant -3 <= xz5 <= gv;
  loop invariant jzd >= 0;
  loop invariant jzd >= xz5;
  loop invariant (jzd + xz5) >= 7;
  loop invariant (jzd + xz5 + 1) % 8 == 0;
  loop assigns jzd, xz5;
*/
while (xz5<gv) {
      jzd += jzd;
      jzd = jzd + xz5;
      xz5++;
  }
}