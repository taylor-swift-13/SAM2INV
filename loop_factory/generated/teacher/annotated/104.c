int main1(int m){
  int n, q, v;

  n=(m%14)+9;
  q=0;
  v=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant m == \at(m,Pre);
  loop invariant n == (m % 14) + 9;
  loop invariant q >= 0;
  loop invariant (q == 0) ==> (v == 6);
  loop invariant (q != 0) ==> (v == q - 3);
  loop invariant q % 3 == 0;

  loop invariant v == 6 || v == q - 3;
  loop invariant n == \at(m, Pre) % 14 + 9;

  loop invariant (q == 0 && v == 6) || (q != 0 && v == q - 3);

  loop invariant v >= q - 3;
  loop assigns v, q;
*/
while (q<=n-3) {
      v = v-v;
      v = v+q;
      q = q+3;
  }

}
