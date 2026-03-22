int main1(int u,int g){
  int i, tjk, yy, ro, hb, gz;

  i=u+13;
  tjk=0;
  yy=0;
  ro=0;
  hb=0;
  gz=0;

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
