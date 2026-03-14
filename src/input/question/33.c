int main1(int a,int b,int q){
  int r, z, v, m, g, l;

  r=q;
  z=0;
  v=8;
  m=b;
  g=0;
  l=q;


while (1) {
      if (v>=r) {
          break;
      }
      if (g<=m) {
          m = g;
      }
      v = v+1;
      v = v*2;
  }
/*@
  assert (g == 0);
*/

  while (v > r) {
      v = v - 1;
      z = z + 1;
  }
/*@
  assert !(v > r) &&
         (v == r);
*/
}
