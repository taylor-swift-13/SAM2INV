int main1(){
  int g9, ga20, d, ry8h, wc, s6, ld;

  g9=1*3;
  ga20=g9;
  d=15;
  ry8h=0;
  wc=ga20;
  s6=g9;
  ld=0;

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
