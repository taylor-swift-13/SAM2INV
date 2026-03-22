int main1(){
  int mpz, r8n, xuc, d, gx8, i;
  mpz=1+14;
  r8n=mpz;
  xuc=0;
  d=0;
  gx8=13;
  i=mpz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= xuc <= mpz;
  loop invariant d == xuc*(xuc-1)/2;
  loop invariant (i == mpz);
  loop invariant gx8 == 13 + ((xuc*(xuc+1))/2) + (2*i*xuc);
  loop assigns d, xuc, gx8;
*/
while (1) {
      if (!(xuc<mpz)) {
          break;
      }
      d += xuc;
      xuc = xuc + 1;
      gx8 += xuc;
      gx8 = gx8+i+i;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r8n >= 15;
  loop invariant gx8 >= 0;
  loop invariant d >= 105;
  loop invariant gx8 <= 583;
  loop assigns d, r8n, gx8;
*/
for (; gx8-5>=0; gx8 = gx8 - 5) {
      d++;
      r8n += d;
      r8n += r8n;
      d = d + gx8;
  }
}