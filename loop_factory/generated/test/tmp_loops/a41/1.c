int main1(int s){
  int ux4, zq, cd, ff, km, ys, da, w, rek;

  ux4=53;
  zq=0;
  cd=0;
  ff=ux4;
  km=s;
  ys=zq;
  da=zq;
  w=ux4;
  rek=ux4;

  while (cd<ux4&&ff>0) {
      ff--;
      cd++;
      if (da<ys+3) {
          ys += 1;
      }
      if (zq+7<=s+ux4) {
          km += ys;
      }
      da += 1;
      w = w + 3;
      rek = rek + zq;
      ys = ys + da;
      ys = km-ys;
      da += km;
      rek = rek + da;
  }

}
