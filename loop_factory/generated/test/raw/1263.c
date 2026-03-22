int main1(int k){
  int w, nm, vr, hqz, g9;

  w=60;
  nm=2;
  vr=-5;
  hqz=1;
  g9=w;

  while (nm<=w) {
      vr = vr*nm;
      if (nm<w) {
          hqz = hqz*nm;
      }
      g9 = g9 + w;
      nm = nm + 1;
  }

}
