int main1(){
  int os, yeo, oqj, vc, w7, bc, rh, qlb;

  os=1+19;
  yeo=0;
  oqj=12;
  vc=14;
  w7=0;
  bc=-2;
  rh=0;
  qlb=5;

  while (1) {
      if (!(yeo<os)) {
          break;
      }
      if (w7==0) {
          oqj += 2;
          vc -= 2;
          w7 = 1;
      }
      else {
          oqj -= 2;
          vc += 2;
          w7 = 0;
      }
      yeo = yeo + 1;
      if (rh+7<os) {
          rh += 1;
      }
      bc = bc + yeo;
      qlb = qlb + 3;
      bc += 4;
  }

}
