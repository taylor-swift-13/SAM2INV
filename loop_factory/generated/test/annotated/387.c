int main1(){
  int col, yc, ja, b1;
  col=1;
  yc=col;
  ja=col;
  b1=col;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant col == 1;
  loop invariant b1 == 1;
  loop invariant (yc == 1) || (yc == 2);
  loop invariant 0 <= ja - col;
  loop invariant ja - col <= b1;
  loop invariant ((yc == 1) ==> (ja == col)) && ((yc == 2) ==> (ja == 2*col));
  loop assigns ja, yc;
*/
while (yc>=3) {
      if (!(!(yc<col/2))) {
          ja += 1;
      }
      else {
          ja = ja + b1;
      }
      yc = 2;
  }
}