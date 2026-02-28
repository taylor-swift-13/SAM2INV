int main1(int n,int q){
  int e, v, f, x;

  e=79;
  v=e;
  f=-6;
  x=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == -6 + (79 - v) * (2*x + 1);
  loop invariant x == n;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= v;
  loop invariant v <= 79;
  loop invariant v >= 0;
  loop invariant f == -6 + (2*x + 1) * (79 - v);
  loop invariant e == 79;
  loop assigns f, v;
*/
while (v>=1) {
      f = f+x+x;
      f = f+1;
      v = v-1;
  }

}
