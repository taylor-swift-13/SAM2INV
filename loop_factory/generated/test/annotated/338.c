int main1(){
  int v, l, w, nd, z, b;
  v=50;
  l=0;
  w=-3;
  nd=1;
  z=0;
  b=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 50;
  loop invariant w <= v;
  loop invariant -3 <= w;
  loop invariant nd <= v;
  loop invariant z == w*(w+1)/2 - 3;
  loop assigns nd, w, z;
*/
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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b <= z;
  loop assigns b, nd, v;
*/
while (1) {
      if (!(b<=z-1)) {
          break;
      }
      b += 1;
      nd += z;
      v++;
  }
}