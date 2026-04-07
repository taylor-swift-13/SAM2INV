int main1(int z){
  int c29, o, t, wz;

  c29=21;
  o=0;
  t=0;
  wz=0;

  while (1) {
      if (!(t < z)) {
          break;
      }
      o = (o + 1) % c29;
      t += 1;
      wz = wz + o;
  }

}
