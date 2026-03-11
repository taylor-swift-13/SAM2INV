int main1(){
  int v, zgh, dyks, o, w;
  v=1;
  zgh=1;
  dyks=1;
  o=0;
  w=0;

while (dyks<=v) {
      o = o+dyks*dyks;
      dyks += 1;
      w = (w+v)+(-(zgh));
  }

while (1) {
      zgh += 1;
      if (zgh>=dyks) {
          break;
      }
  }
/*@
  assert (o == (dyks-1)*dyks*(2*dyks-1)/6);
*/

}