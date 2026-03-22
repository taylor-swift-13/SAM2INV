int main1(int w){
  int tn7, ec, niv, j3, z, ma, yi;

  tn7=51;
  ec=0;
  niv=0;
  j3=1;
  z=6;
  ma=0;
  yi=ec;

  while (1) {
      if (!(ma<=tn7)) {
          break;
      }
      niv = niv + j3;
      ma += 1;
      j3 += z;
      z += 4;
      w += ma;
      yi = yi+j3+z;
  }

}
