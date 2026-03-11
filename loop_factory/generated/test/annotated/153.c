int main1(){
  int nz, h, gc;
  nz=1*3;
  h=0;
  gc=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gc == 5*h + 16;
  loop invariant 0 <= h;
  loop invariant h <= nz;
  loop assigns gc, h;
*/
while (1) {
      if (!(h<=nz-1)) {
          break;
      }
      gc = gc + 5;
      h += 1;
  }
}