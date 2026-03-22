int main1(int d,int l){
  int my1, n, nu, e7q;
  my1=l*2;
  n=my1+7;
  nu=13;
  e7q=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (my1 == 0) || (my1 == 2*l);
  loop invariant n == 2*l + 7;
  loop invariant (nu == e7q*e7q) || (nu == 13);
  loop invariant e7q >= -8;
  loop invariant (nu == e7q*e7q) || (nu == 13 && e7q == -8);
  loop assigns e7q, nu, my1;
*/
while (n-my1>0) {
      e7q += 1;
      nu = e7q*e7q;
      my1 = 0;
  }
}