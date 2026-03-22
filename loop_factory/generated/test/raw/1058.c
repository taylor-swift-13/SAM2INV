int main1(int e,int z){
  int v1, u, uy, u8, w1;

  v1=76;
  u=0;
  uy=0;
  u8=0;
  w1=e;

  while (uy<v1) {
      u = u + e;
      uy++;
      e += 2;
      w1 += uy;
  }

  while (u<uy) {
      v1 = v1+u8*u;
      z = z+(v1%7);
      u8 += 1;
      u = uy;
  }

}
