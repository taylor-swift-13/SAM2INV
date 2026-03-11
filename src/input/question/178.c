int main1(int m,int n){
  int r, u, v, p;

  r=53;
  u=r;
  v=r;
  p=6;


while (u>1) {
      v = v*2;
      u = u-2;
  }
/*@
  assert !(u>1) &&
         (v % 53 == 0);
*/

}
