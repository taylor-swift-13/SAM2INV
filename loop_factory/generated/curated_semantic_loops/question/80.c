int main1(int m,int n){
  int z, u, w, r;

  z=8;
  u=z+6;
  w=u;
  r=z;


while (u>=z+1) {
      w = w*2;
      r = r+w;
      r = r%2;
      u = u-2;
  }
/*@
  assert !(u>=z+1) &&
         (z == 8);
*/

}
