int main1(int o,int x){
  int u, yv, g4, e, bz, zuk, ip, u3w, n1;

  u=x+11;
  yv=0;
  g4=0;
  e=0;
  bz=0;
  zuk=0;
  ip=0;
  u3w=0;
  n1=0;

  while (yv<u+(x%7)) {
      if (!(!(yv%9==0))) {
          if (yv%4==0) {
              e += 1;
              u3w += 2;
          }
          else {
              if (yv%3==0) {
                  bz++;
                  u3w = u3w + 3;
              }
              else {
                  if (yv%2==0) {
                      zuk++;
                      u3w += 4;
                  }
                  else {
                      if (1) {
                          ip++;
                          u3w = u3w + 5;
                      }
                  }
              }
          }
      }
      else {
          g4 += 1;
          u3w += 1;
      }
      yv += 1;
      n1 = n1+yv%9;
  }

}
