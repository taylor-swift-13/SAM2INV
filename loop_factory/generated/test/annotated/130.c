int main1(){
  int s, nf, n, mv;
  s=1;
  nf=0;
  n=6;
  mv=13;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mv == 13 + 7*nf;
  loop invariant n == 6 + 7*nf;
  loop invariant s == 1;
  loop invariant nf >= 0;
  loop invariant nf <= s;
  loop assigns mv, n, nf;
*/
while (1) {
      if (!(nf<=s-1)) {
          break;
      }
      mv = mv + 7;
      n = n + 7;
      nf += 1;
  }
}