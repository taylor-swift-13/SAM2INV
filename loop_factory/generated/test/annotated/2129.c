int main1(){
  int niho, e1h, z, q;
  niho=1;
  e1h=0;
  z=niho;
  q=e1h;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == e1h * niho;
  loop invariant z == 1 - (e1h % 2);
  loop invariant 0 <= e1h;
  loop invariant e1h <= niho;
  loop invariant z == (niho + e1h) % 2;
  loop assigns q, z, e1h;
*/
while (1) {
      if (!(e1h < niho)) {
          break;
      }
      q += niho;
      z = 1-z;
      e1h += 1;
  }
}