int main1(int v){
  int h0, puv, muh, j1, sr, dj, pz, rt;

  h0=37;
  puv=h0;
  muh=1;
  j1=1;
  sr=1;
  dj=1;
  pz=0;
  rt=v;

  while (1) {
      if (!(sr<=h0)) {
          break;
      }
      muh = muh*(v/sr);
      if ((sr/2)%2==0) {
          dj = 1;
      }
      else {
          dj = -1;
      }
      sr++;
      j1 = j1+dj*muh;
      muh = muh*(v/sr);
      if ((puv%4)==0) {
          pz = pz*rt;
      }
      pz = pz*2+4;
      rt += dj;
      rt = rt*pz+4;
  }

}
