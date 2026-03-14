int main1(int y){
  int e7e, cm, mt, g, mz;

  e7e=57;
  cm=e7e;
  mt=1;
  g=0;
  mz=-6;

  while (mt<=e7e) {
      g = g+2*mt-1;
      mt = mt + 1;
      mz = mz + mt;
  }

  while (mt<mz) {
      mt = mt + 1;
      cm = mz-mt;
      y = y + mt;
  }

}
