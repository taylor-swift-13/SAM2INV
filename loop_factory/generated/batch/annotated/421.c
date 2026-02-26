int main1(int a,int q){
  int r, t, v, n;

  r=q;
  t=0;
  v=t;
  n=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == q;
  loop invariant n == q;
  loop invariant q == \at(q, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant n + v <= q;
  loop invariant n <= q;
  loop invariant v >= 0;
  loop assigns v, n;
*/
while (v!=0&&n!=0) {
      if (v>n) {
          v = v-n;
      }
      else {
          n = n-v;
      }
  }

}
