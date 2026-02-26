int main1(int b,int n){
  int k, i, v, d;

  k=67;
  i=0;
  v=k;
  d=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == k + i;
  loop invariant 0 <= i;
  loop invariant i <= k;
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == 67;
  loop invariant i >= 0;
  loop invariant v == i + k;
  loop assigns i, v;
*/
while (1) {
      if (i>=k) {
          break;
      }
      v = v+1;
      i = i+1;
  }

}
