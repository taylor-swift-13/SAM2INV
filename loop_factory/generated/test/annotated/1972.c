int main1(int v){
  int ka, w, z, gsx;
  ka=53;
  w=0;
  z=w;
  gsx=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == (\at(v, Pre) + w * gsx);
  loop invariant z == w;
  loop invariant gsx == \at(v, Pre);
  loop invariant 0 <= w;
  loop invariant w <= ka;
  loop assigns z, v, w;
*/
while (1) {
      if (!(w < ka)) {
          break;
      }
      z += 1;
      v += gsx;
      w += 1;
  }
}