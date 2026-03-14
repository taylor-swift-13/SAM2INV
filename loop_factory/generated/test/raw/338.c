int main1(){
  int v, l, w, nd, z, b;

  v=50;
  l=0;
  w=-3;
  nd=1;
  z=0;
  b=l;

  while (1) {
      if (!(w<=v-1)) {
          break;
      }
      if (z<v) {
          nd = w;
      }
      w += 1;
      z = z + w;
  }

  while (1) {
      if (!(b<=z-1)) {
          break;
      }
      b += 1;
      nd += z;
      v++;
  }

}
