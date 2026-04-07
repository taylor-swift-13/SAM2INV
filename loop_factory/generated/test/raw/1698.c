int main1(int z){
  int yx, fa, ifq;

  yx=z;
  fa=0;
  ifq=fa;

  while (fa < yx) {
      ifq += 2;
      z += 2;
      fa++;
      ifq += z;
  }

}
