int main1(int c,int f){
  int rk, ke, df9a, z6n, lttr;
  rk=78;
  ke=0;
  df9a=1;
  z6n=6;
  lttr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z6n == 6 + 2*lttr;
  loop invariant df9a == lttr*lttr + 5*lttr + 1;
  loop invariant c == \at(c,Pre) + 2*lttr*lttr + 14*lttr;
  loop invariant ke == (lttr*lttr*lttr + 6*lttr*lttr - 4*lttr) / 3;
  loop invariant 0 <= lttr;
  loop invariant lttr <= rk + 1;
  loop invariant f >= \at(f,Pre);
  loop invariant f <= \at(f,Pre) + 5*lttr;
  loop assigns c, f, ke, df9a, z6n, lttr;
*/
while (1) {
      if (!(lttr<=rk)) {
          break;
      }
      ke += df9a;
      lttr++;
      df9a += z6n;
      z6n += 2;
      c = c+z6n+z6n;
      f = f+(df9a%6);
  }
}