int main1(){
  int cb, vsl, e, y, mp, ujw;
  cb=1+4;
  vsl=0;
  e=0;
  y=vsl;
  mp=vsl;
  ujw=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ujw == -6 + cb*e - (e*(e-1))/2;
  loop invariant 0 <= e;
  loop invariant e <= cb;
  loop assigns e, y, ujw;
*/
while (1) {
      if (!(e<cb)) {
          break;
      }
      y = cb-e;
      ujw = ujw + y;
      e += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cb >= mp;
  loop invariant 0 <= e;
  loop invariant e <= cb;
  loop assigns cb, e;
*/
while (1) {
      if (!(cb<mp)) {
          break;
      }
      e = (mp)+(-(cb));
      e = e - e;
      cb += 1;
  }
}