int main1(int n,int q){
  int d, k, v;

  d=78;
  k=1;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == 78;
  loop invariant k <= d;
  loop invariant k % 3 == 1;
  loop invariant k*k - 3*k + 6*v == 6*q - 2;
  loop invariant q == \at(q, Pre);
  loop invariant v == q - ((k - 1) * (k - 2)) / 6;
  loop invariant n == \at(n, Pre);
  loop invariant 1 <= k;
  loop invariant k <= d - 2;
  loop invariant v >= q - 925;
  loop invariant (n == \at(n, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant ((k - 1) % 3 == 0);
  loop invariant (k <= d);
  loop invariant (v <= \at(q, Pre));
  loop assigns k, v;
*/
while (k<=d-3) {
      v = v-k;
      k = k+3;
  }

}
