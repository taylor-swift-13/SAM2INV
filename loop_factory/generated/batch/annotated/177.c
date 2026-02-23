int main1(int k,int n){
  int c, q, l;

  c=65;
  q=c;
  l=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 65 || l == 0;
  loop invariant q % 2 == 1;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant c == 65;
  loop invariant 0 <= q;
  loop invariant q <= c;
  loop invariant 0 <= q <= c;
  loop invariant q % 2 == c % 2;
  loop assigns l, q;
*/
while (q>=2) {
      l = l+q;
      l = l-l;
      q = q-2;
  }

}
