int main1(){
  int w, z, pq2a, xb;
  w=1;
  z=0;
  pq2a=0;
  xb=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xb == z % 3;
  loop invariant pq2a == z + z / 3;
  loop invariant w == 1;
  loop invariant 0 <= z <= w;
  loop invariant 0 <= xb < 3;
  loop assigns pq2a, xb, z;
*/
for (; z<w; z += 1) {
      pq2a = pq2a + 1;
      xb += 1;
      if (xb>=3) {
          xb = xb - 3;
          pq2a = pq2a + 1;
      }
  }
}