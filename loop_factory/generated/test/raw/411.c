int main1(){
  int fv, kn2o, mz, awd, g, l5;

  fv=16;
  kn2o=0;
  mz=34;
  awd=0;
  g=1;
  l5=0;

  while (mz>0&&kn2o<fv) {
      if (mz<=g) {
          l5 = mz;
      }
      else {
          l5 = g;
      }
      g++;
      kn2o = kn2o + 1;
      awd = awd + l5;
      mz = mz - l5;
  }

}
