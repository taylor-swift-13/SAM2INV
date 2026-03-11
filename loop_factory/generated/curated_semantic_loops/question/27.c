int main1(){
  int v, zgh, dyks, o, w;
  v=1;
  zgh=1;
  dyks=1;
  o=0;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */

while (dyks<=v) {
      o = o+dyks*dyks;
      dyks += 1;
      w = (w+v)+(-(zgh));
  }
  /* >>> LOOP INVARIANT TO FILL <<< */

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