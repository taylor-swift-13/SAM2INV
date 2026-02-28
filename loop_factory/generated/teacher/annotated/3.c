int main1(int m,int n){
  int e, s, q, w, v, t;

  e=48;
  s=0;
  q=3;
  w=s;
  v=n;
  t=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s <= e;
  loop invariant q - s == 3;
  loop invariant 0 <= s;
  loop invariant e == 48;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == s + 3;
  loop invariant s >= 0;
  loop assigns s, q;
*/
while (s<e) {
      q = q+1;
      s = s+1;
  }

}
