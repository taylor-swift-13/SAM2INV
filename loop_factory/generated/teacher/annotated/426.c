int main1(int m,int p){
  int n, v, c;

  n=49;
  v=0;
  c=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (c == \at(p, Pre) || c == 0);
  loop invariant n == 49;
  loop invariant v == 0;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v <= n;
  loop invariant 0 <= v;
  loop invariant c == p || c == 0;
  loop invariant (((c == p) || (c == 0)) && (0 <= v) && (v <= n));
  loop assigns c;
*/
while (v<n) {
      c = c+4;
      c = c-c;
      if (m<c+3) {
          c = c+v;
      }
  }

}
