int main1(int i){
  int r0ln, a1, t3, z;

  r0ln=i+16;
  a1=1;
  t3=-8;
  z=4;

  while (1) {
      if (!(t3<r0ln)) {
          break;
      }
      if (t3<r0ln) {
          t3 += 1;
      }
      i = i+r0ln-a1;
      z += 1;
  }

}
