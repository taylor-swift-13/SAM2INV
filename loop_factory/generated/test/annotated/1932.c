int main1(){
  int jcu, f, rg3, yir9;
  jcu=10;
  f=0;
  rg3=1;
  yir9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (f >= 0);
  loop invariant (f <= jcu);
  loop invariant (jcu == 10);
  loop invariant ((f * f + f + 2 * yir9) == (4 * rg3 - 4));
  loop invariant (rg3 >= 1);
  loop invariant (yir9 >= 0);
  loop assigns f, rg3, yir9;
*/
while (f < jcu) {
      f = f + 1;
      rg3 = 2*rg3 + f;
      yir9 += rg3;
  }
}