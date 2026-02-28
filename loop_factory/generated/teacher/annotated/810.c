int main1(int n,int q){
  int f, j, p, v;

  f=q+25;
  j=0;
  p=q;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(q, Pre) + 4 * j;
  loop invariant v == 2 - j;

  loop invariant f == \at(q, Pre) + 25;
  loop invariant q == \at(q, Pre);
  loop invariant p == q + 4*j;
  loop invariant f == q + 25;
  loop invariant j >= 0;
  loop invariant n == \at(n, Pre);
  loop invariant 0 <= j;
  loop assigns p, j, v;
*/
while (1) {
      if (j>=f) {
          break;
      }
      p = p+3;
      j = j+1;
      p = p+1;
      v = v-1;
  }

}
