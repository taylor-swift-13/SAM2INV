int main1(int r,int c){
  int ihf, zh, kf, sd9, rg5, ai, ixup, b3t, awed;
  ihf=r;
  zh=0;
  kf=0;
  sd9=0;
  rg5=0;
  ai=0;
  ixup=0;
  b3t=0;
  awed=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b3t == zh;
  loop invariant zh >= 0;
  loop invariant r >= \at(r, Pre);
  loop invariant 0 <= rg5;
  loop invariant 0 <= sd9;
  loop invariant 0 <= ai;
  loop invariant 0 <= ixup;
  loop invariant 0 <= kf;
  loop invariant 0 <= awed;
  loop invariant ihf == \at(r, Pre);
  loop invariant rg5 <= zh;
  loop assigns r, c, awed, b3t, zh, rg5, sd9, ai, ixup, kf;
*/
while (zh<ihf) {
      if (!(!(zh%11==0))) {
          if (zh%10==0) {
              sd9 += 1;
          }
          else {
              if (zh%7==0) {
                  rg5 = rg5 + 1;
              }
              else {
                  if (zh%4==0) {
                      ai++;
                  }
                  else {
                      if (1) {
                          ixup++;
                      }
                  }
              }
          }
      }
      else {
          kf += 1;
      }
      zh++;
      c = (c+rg5)%7;
      awed = awed+zh%7;
      b3t++;
      r += rg5;
  }
}