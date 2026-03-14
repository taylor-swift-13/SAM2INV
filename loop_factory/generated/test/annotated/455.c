int main1(int n){
  int k3b6, h7, q, ur5m;
  k3b6=n;
  h7=0;
  q=0;
  ur5m=k3b6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre) + 2 * q &&
                     h7 == q * \at(n, Pre) + q * (q - 1);
  loop invariant n == \at(n, Pre) + 2*q;
  loop invariant h7 == q * \at(n, Pre) + q*(q-1);
  loop assigns h7, q, ur5m, n;
*/
while (q<k3b6) {
      h7 += n;
      q += 1;
      ur5m = ur5m+(h7%5);
      n += 2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k3b6 <= q;
  loop invariant n == \at(n, Pre) + 2 * q;
  loop assigns ur5m, h7, k3b6;
*/
while (1) {
      if (!(k3b6<q)) {
          break;
      }
      ur5m = ur5m+h7*k3b6;
      h7 += k3b6;
      k3b6 = q;
  }
}