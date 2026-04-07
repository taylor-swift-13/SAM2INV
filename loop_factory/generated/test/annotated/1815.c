int main1(int l){
  int rdu, k0a, zy, ewg;
  rdu=60;
  k0a=0;
  zy=k0a;
  ewg=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zy  == 3*k0a;
  loop invariant ewg == \at(l,Pre) + k0a*(k0a+1)/2;
  loop invariant ewg == l + k0a*(k0a + 1)/2;
  loop invariant k0a >= 0;
  loop invariant rdu + k0a*k0a == 60;
  loop assigns rdu, k0a, zy, ewg;
*/
while (1) {
      if (!(rdu > 0)) {
          break;
      }
      rdu = rdu - (2*k0a + 1);
      k0a = k0a + 1;
      zy = zy + 3;
      ewg = (k0a)+(ewg);
  }
}