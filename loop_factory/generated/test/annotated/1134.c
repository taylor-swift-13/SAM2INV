int main1(){
  int k4m, c2, s, xg, b, j, d29g;
  k4m=76;
  c2=-2;
  s=0;
  xg=0;
  b=0;
  j=4;
  d29g=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d29g == c2 + 2;
  loop invariant 0 <= b;
  loop invariant b <= d29g;
  loop invariant 0 <= xg;
  loop invariant xg <= d29g;
  loop invariant s + b <= d29g;
  loop invariant -2 <= c2 <= k4m;
  loop invariant 0 <= s <= j;
  loop assigns c2, d29g, s, b, xg;
*/
for (; c2<k4m; c2 += 1) {
      if (c2%3==0) {
          if (s>0) {
              s -= 1;
              b += 1;
          }
      }
      else {
          if (s<j) {
              s++;
              xg++;
          }
      }
      d29g++;
  }
}