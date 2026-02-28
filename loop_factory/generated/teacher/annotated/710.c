int main1(int k,int m,int p,int q){
  int o, w, v, z, n, c, f, r;

  o=77;
  w=4;
  v=0;
  z=k;
  n=-5;
  c=p;
  f=3;
  r=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= o;
  loop invariant o == 77;
  loop invariant n == -5 || n == c;

  loop invariant c == p;
  loop invariant p == \at(p, Pre);
  loop invariant (n == -5) || (n == c);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= v;
  loop invariant (n <= -5) || (n <= c);
  loop invariant v >= 0;
  loop invariant (n == -5) || (n == p);
  loop assigns v, n;
*/
while (v<o) {
      v = v+1;
      if (c<=n) {
          n = c;
      }
  }

}
