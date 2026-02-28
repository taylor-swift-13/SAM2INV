int main1(int k,int m,int n,int p){
  int c, i, v, a, f, w, g, q;

  c=n+8;
  i=0;
  v=0;
  a=p;
  f=0;
  w=n;
  g=c;
  q=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == n + 8;
  loop invariant k == \at(k, Pre);
  loop invariant v >= 0;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant c == \at(n, Pre) + 8;
  loop invariant (v == 0) ==> (a == \at(p, Pre));
  loop invariant (v > 0) ==> (a == c - (v - 1));
  loop invariant (v == 0) ==> (a == p);
  loop invariant (v > 0) ==> (a == c - v + 1);
  loop assigns a, v;
*/
while (1) {
      a = c-v;
      v = v+1;
  }

}
