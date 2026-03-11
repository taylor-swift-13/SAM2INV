int main1(){
  int v, zgh, dyks, o, w;
  v=1;
  zgh=1;
  dyks=1;
  o=0;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == (dyks-1)*dyks*(2*dyks-1)/6;
  loop invariant w == (dyks-1)*(v - zgh);
  loop invariant 1 <= dyks;
  loop invariant dyks <= v+1;
  loop invariant v == 1;
  loop invariant zgh == 1;
  loop assigns o, dyks, w;
*/
while (dyks<=v) {
      o = o+dyks*dyks;
      dyks += 1;
      w = (w+v)+(-(zgh));
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 1 <= zgh <= dyks;
  loop assigns zgh;
*/
while (1) {
      zgh += 1;
      if (zgh>=dyks) {
          break;
      }
  }
}