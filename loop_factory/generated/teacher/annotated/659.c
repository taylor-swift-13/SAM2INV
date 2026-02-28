int main1(int a,int q){
  int l, k, u, v, x;

  l=q+11;
  k=1;
  u=8;
  v=l;
  x=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x - u == -4;
  loop invariant u >= 8;
  loop invariant x >= 4;
  loop invariant v <= l;
  loop invariant l == q + 11;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant k == 1;
  loop invariant u - x == 4;
  loop assigns u, v, x;
*/
while (1) {
      if (x<=v) {
          v = x;
      }
      u = u+1;
      v = v-1;
      x = x+1;
      if (u<k+3) {
          v = v-3;
      }
  }

}
