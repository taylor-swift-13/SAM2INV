int main1(){
  int z, uq, xd, h;
  z=9;
  uq=0;
  xd=z;
  h=-3;

while (uq+1<=z) {
      if (!(!(xd+1<=z))) {
          xd++;
      }
      else {
          xd = z;
      }
      h += uq;
      z = (uq+1)-1;
      if ((uq%6)==0) {
          h += uq;
      }
      else {
          h -= h;
      }
  }
/*@
  assert !(uq+1<=z) &&
         (z >= uq);
*/

}