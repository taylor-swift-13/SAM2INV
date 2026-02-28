int main1(int n,int p){
  int l, x, v;

  l=38;
  x=0;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 4 + 5 * x;
  loop invariant 0 <= x;
  loop invariant x <= l;
  loop invariant l == 38;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop assigns v, x;
*/
while (x<l) {
      v = v+1;
      v = v+4;
      x = x+1;
  }

}
