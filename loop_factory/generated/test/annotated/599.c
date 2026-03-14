int main1(){
  int yj, ogl, w, na7, y, pi4f;
  yj=1;
  ogl=0;
  w=0;
  na7=0;
  y=0;
  pi4f=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ogl <= yj;
  loop invariant pi4f == w + na7 + y;
  loop invariant 0 <= w;
  loop invariant 0 <= na7;
  loop invariant 0 <= y;
  loop assigns ogl, w, na7, y, pi4f;
*/
while (1) {
      if (!(ogl<yj)) {
          break;
      }
      if (!(!(ogl%8==0))) {
          if (ogl%7==0) {
              y++;
          }
          else {
              if (ogl%7==0) {
                  na7++;
              }
              else {
                  w += 1;
              }
          }
      }
      else {
          pi4f += 1;
      }
      pi4f = w+na7+y;
      ogl++;
  }
}