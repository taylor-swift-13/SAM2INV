int main1(int a,int b,int n,int q){
  int f, m, p, r, c, v, z;

  f=80;
  m=0;
  p=0;
  r=4;
  c=q;
  v=m;
  z=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 0;
  loop invariant r == 4;
  loop invariant m <= f;
  loop invariant m >= 0;
  loop invariant (m == 0) ==> (c == q);
  loop invariant (m > 0) ==> (c == q % 7);
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (m == 0) ==> (c == q) && (m >= 1) ==> (c == q % 7);
  loop invariant m == 0 ==> c == \at(q, Pre);
  loop invariant m > 0 ==> c == \at(q, Pre) % 7;
  loop assigns p, r, c, m;
*/
while (m<f) {
      p = p*2;
      r = r+p;
      c = c%7;
      m = m+1;
  }

}
