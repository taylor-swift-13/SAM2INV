int main1(int m,int l){
  int z, ha, d, az, wr;

  z=24;
  ha=-2;
  d=-3;
  az=20;
  wr=m*3;

  while (wr<=z) {
      ha += d;
      d = d + az;
      wr += 1;
      az += 6;
      m = m+(az%6);
      l = l + az;
  }

}
