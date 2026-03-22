int main1(){
  int g9, ga20, d, ry8h, wc, s6, ld;
  g9=1*3;
  ga20=g9;
  d=15;
  ry8h=0;
  wc=ga20;
  s6=g9;
  ld=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d + ry8h == 15;
  loop invariant ga20 <= g9;
  loop invariant 0 <= ga20;
  loop invariant ld >= 0;
  loop invariant d >= 0;
  loop invariant ry8h >= 0;
  loop invariant s6 >= 3;
  loop invariant wc >= 3;
  loop assigns d, ry8h, ga20, ld, s6, wc;
*/
while (ga20<g9) {
      if (ga20%2==0) {
          if (d>0) {
              d -= 1;
              ry8h += 1;
          }
      }
      else {
          if (ry8h>0) {
              ry8h = ry8h - 1;
              d++;
          }
      }
      ga20++;
      ld = ld+(ga20%2);
      s6 += ld;
      ld += wc;
      wc += ga20;
  }
}