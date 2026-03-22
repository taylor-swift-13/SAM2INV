int main1(int j){
  int qv, mu3, ak, s, caf, r4, tifk, ln;

  qv=j-1;
  mu3=qv;
  ak=4;
  s=4;
  caf=0;
  r4=5;
  tifk=0;
  ln=2;

  while (1) {
      if (!(mu3<qv)) {
          break;
      }
      if (!(!(mu3%3==0))) {
          if (ak>0) {
              ak--;
              caf++;
          }
      }
      else {
          if (ak<r4) {
              ak = ak + 1;
              s++;
          }
      }
      mu3++;
      ln += ak;
      tifk++;
      r4 = r4*2;
      ln = ln/2;
  }

}
