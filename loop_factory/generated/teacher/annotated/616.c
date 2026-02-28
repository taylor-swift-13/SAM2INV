int main1(int m,int p){
  int l, u, v, j, b, s;

  l=p+14;
  u=l+3;
  v=m;
  j=-6;
  b=-4;
  s=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == p + 14;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant j <= -4;
  loop invariant j >= -6;
  loop invariant v <= m;
  loop invariant -6 <= j;
  loop invariant b == -4;
  loop invariant j == -6;
  loop assigns j, v;
*/
while (1) {
      if (v>=l) {
          break;
      }
      if (b<=j) {
          j = b;
      }
      v = v+1;
      v = v+j;
  }

}
