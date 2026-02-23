int main1(int n,int q){
  int b, l, v;

  b=(n%21)+8;
  l=0;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 0;

  loop invariant v == b;
  loop invariant b == (n % 21) + 8;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant -12 <= b;
  loop invariant b <= 28;
  loop assigns v, l;
*/
while (b>=b) {
      v = v+l;
      l = l;
  }

}
