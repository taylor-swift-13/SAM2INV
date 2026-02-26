int main1(int n,int q){
  int d, k, v;

  d=78;
  k=d;
  v=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k >= 0;
  loop invariant k <= d;
  loop invariant n == \at(n,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant d == 78;
  loop invariant 0 <= k <= d;
  loop invariant k <= 78;

  loop invariant 0 <= k <= 78;
  loop assigns k;
*/
while (k-1>=0) {
      k = k-1;
  }

}
