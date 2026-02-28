int main1(int b,int k,int m,int p){
  int h, u, v, e;

  h=p+22;
  u=0;
  v=p;
  e=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == p + 22;
  loop invariant p <= v;
  loop invariant v <= h + 1;
  loop invariant v >= p;
  loop invariant v <= h;
  loop invariant ((v - p) % 2 == 0);
  loop invariant ((v - p) % 2) == 0;
  loop invariant (v - p) % 2 == 0;
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop assigns v;
*/
while (v<h) {
      if (v<h) {
          v = v+1;
      }
      v = v+1;
  }

}
