int main1(int l,int x){
  int jy6, kav, qb, z9, k, o2;

  jy6=11;
  kav=0;
  qb=0;
  z9=0;
  k=0;
  o2=0;

  while (kav<=jy6-1) {
      if (!(!(kav%7==0))) {
          if (kav%9==0) {
              k += 1;
          }
          else {
              if (kav%7==0) {
                  z9 += 1;
              }
              else {
                  qb++;
              }
          }
      }
      else {
          o2 += 1;
      }
      kav++;
      l += kav;
  }

  while (1) {
      if (!(z9<=qb-1)) {
          break;
      }
      k = k + z9;
      kav = kav + k;
      z9 += 1;
      o2 += 2;
      x = x + 3;
      o2 += 1;
  }

}
