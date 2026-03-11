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

  int __aux_2=0;
  while (__aux_2 < 4) { __aux_2 = __aux_2 + 1; }
}
