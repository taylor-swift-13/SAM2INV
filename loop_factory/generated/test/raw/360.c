int main1(int r){
  int y5, kro, r2az, elm, z;

  y5=(r%16)+9;
  kro=0;
  r2az=0;
  elm=0;
  z=(r%18)+5;

  while (1) {
      if (!(z>0)) {
          break;
      }
      elm = elm+r*r;
      r2az = r2az+r*r;
      kro = kro+r*r;
      z = z - 1;
      r += y5;
  }

  while (r2az>y5) {
      r2az -= y5;
      y5 = y5 + 1;
      r += y5;
  }

}
