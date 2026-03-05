int main1(){
  int w, z, pq2a, xb;

  w=1;
  z=0;
  pq2a=0;
  xb=0;

  for (; z<w; z += 1) {
      pq2a = pq2a + 1;
      xb += 1;
      if (xb>=3) {
          xb = xb - 3;
          pq2a = pq2a + 1;
      }
  }

}
