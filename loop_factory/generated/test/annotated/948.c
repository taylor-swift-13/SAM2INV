int main1(int u,int g){
  int i, tjk, yy, ro, hb, gz;
  i=u+13;
  tjk=0;
  yy=0;
  ro=0;
  hb=0;
  gz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hb + ro + yy + gz == tjk;
  loop invariant (tjk <= i) || (i <= 0);
  loop invariant g == \at(g,Pre) + i * tjk;
  loop invariant gz == tjk - (tjk + 8) / 9;
  loop invariant 0 <= gz;
  loop invariant 0 <= hb;
  loop invariant 0 <= ro;
  loop invariant 0 <= yy;
  loop assigns tjk, g, gz, hb, ro, yy;
*/
while (1) {
      if (!(tjk<i)) {
          break;
      }
      if (!(!(tjk%9==0))) {
          if (tjk%7==0) {
              hb++;
          }
          else {
              if (tjk%4==0) {
                  ro = ro + 1;
              }
              else {
                  yy += 1;
              }
          }
      }
      else {
          gz = gz + 1;
      }
      tjk += 1;
      g = g + i;
  }
}