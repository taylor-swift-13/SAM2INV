int main1(int m,int q){
  int n, k, o, s;

  n=q-4;
  k=0;
  o=0;
  s=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(q, Pre) - 4;
  loop invariant s >= n;
  loop invariant o == 0 || o == s*s + 1;
  loop invariant (s == n && o == 0) || o == s*s + 1;
  loop invariant s >= n && n == \at(q, Pre) - 4 && q == \at(q, Pre) && m == \at(m, Pre);
  loop invariant q == \at(q, Pre) && m == \at(m, Pre);
  loop invariant n == (\at(q, Pre) - 4);
  loop invariant o == 0 || o == (s*s + 1);
  loop invariant o >= 0;
  loop invariant (s == n) ==> o == 0;
  loop invariant (s > n) ==> o == s*s + 1;
  loop assigns s, o;
*/
while (1) {
      s = s+1;
      o = s*s;
      o = o+1;
  }

}
