int main1(int k,int n,int p){
  int l, y, v, q, o, g;

  l=(n%7)+20;
  y=0;
  v=n;
  q=8;
  o=y;
  g=p;


while (1) {
      if (v>=l) {
          break;
      }
      if (o<=q) {
          q = o;
      }
      v = v+1;
  }
/*@
  assert (o == 0);
*/

  while (q < v) {
      q = q + 1;
      y = y + 1;
  }
/*@
  assert !(q < v) &&
         (q == v);
*/
}
