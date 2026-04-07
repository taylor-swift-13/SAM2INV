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
