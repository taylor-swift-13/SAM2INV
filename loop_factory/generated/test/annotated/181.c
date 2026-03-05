int main1(){
  int py, hx, kgm, ps5;
  py=17;
  hx=py;
  kgm=-5;
  ps5=hx;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hx == 17;
  loop invariant py == 17;
  loop invariant ps5 >= 17;
  loop invariant kgm == (ps5*(ps5+1)*(ps5+2))/3 - 1943;
  loop assigns ps5, kgm;
*/
while (hx>=1) {
      ps5++;
      kgm = kgm+ps5*ps5;
      kgm += ps5;
  }
}