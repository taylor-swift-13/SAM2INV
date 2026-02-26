int main1(int n,int q){
  int k, i, t, v;

  k=q+13;
  i=0;
  t=-1;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == -1 + 8*i;
  loop invariant v >= -1 + i;
  loop invariant v <= -1 + i + i*(i+1)/2;
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant i >= 0;
  loop invariant t == -1 + 8*i && i >= 0 && (k < 0 || i <= k) && q == \at(q, Pre) && n == \at(n, Pre);
  loop invariant v >= i - 1;
  loop invariant k == q + 13;
  loop invariant k == \at(q, Pre) + 13;

  loop invariant v == -1 + i + i*(i+1)/2;
  loop invariant v <= (i*i + 3*i - 2)/2;

  loop assigns i, t, v;
*/
while (1) {
      if (i>=k) {
          break;
      }
      t = t+3;
      i = i+1;
      t = t+4;
      v = v+1;
      t = t+1;
      if (i+4<=t+k) {
          v = v+i;
      }
  }

}
