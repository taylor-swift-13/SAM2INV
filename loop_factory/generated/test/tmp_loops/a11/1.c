int main1(int u){
  int ksc9, dz, jue8, p1j2;

  ksc9=u;
  dz=3;
  jue8=3;
  p1j2=1;

  while (dz<ksc9) {
      if (jue8>=8) {
          p1j2 = -1;
      }
      if (jue8<=3) {
          p1j2 = 1;
      }
      dz = dz + 1;
      jue8 = jue8 + p1j2;
  }

}
