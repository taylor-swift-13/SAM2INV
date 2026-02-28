int main1(int p,int q){
  int l, c, v;

  l=p+24;
  c=0;
  v=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == c*(c+3)/2;
  loop invariant 0 <= c;
  loop invariant l == p + 24;
  loop invariant v >= 0;

  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 2*v == c*c + 3*c;

  loop invariant c >= 0;
  loop invariant v >= c*(c+1)/2;
  loop invariant v <= c*(c+3)/2;
  loop assigns c, v;
*/
while (c<=l-1) {
      v = v+c;
      if (c+2<=l+l) {
          v = v+1;
      }
      v = v+1;
      c = c+1;
  }

}
