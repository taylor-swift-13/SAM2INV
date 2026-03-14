int main1(int k,int p){
  int r, c, v, y, l, s;

  r=30;
  c=r+3;
  v=r;
  y=-8;
  l=k;
  s=r;


while (1) {
      if (v>=r) {
          break;
      }
      if (l<=y) {
          y = l;
      }
      v = v+1;
      v = v+c;
  }
/*@
  assert (r == 30);
*/

  while (y < 0) {
      y = y + 1;
      v = v + 1;
  }
/*@
  assert !(y < 0) &&
         (y == 0);
*/
}
