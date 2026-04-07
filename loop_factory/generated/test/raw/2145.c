int main1(int s){
  int x4mk, z, y83, jm, a;

  x4mk=73;
  z=0;
  y83=0;
  jm=0;
  a=s;

  while (1) {
      if (!(z < x4mk)) {
          break;
      }
      y83 = (1 - (z % 2)) * a + (z % 2) * y83;
      jm = (z % 2) * a + (1 - (z % 2)) * jm;
      a = a + jm;
      z += 1;
  }

}
