int main1(int a,int m){
  int r, k, v;

  r=10;
  k=1;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 1 <= k;
  loop invariant k <= r;
  loop invariant r == 10;
  loop invariant r - k >= 0;
  loop invariant k >= 1;
  loop assigns k;
*/
while (k*3<=r) {
      k = k*3;
  }

}
