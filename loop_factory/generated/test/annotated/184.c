int main1(){
  int ihk, fg, p2, y3vw;
  ihk=1;
  fg=ihk;
  p2=ihk;
  y3vw=ihk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fg == 1;
  loop invariant ihk == 1;
  loop invariant y3vw >= 1;
  loop invariant p2 >= (y3vw*y3vw)*(y3vw*y3vw);
  loop assigns y3vw, p2;
*/
while (fg-2>=0) {
      y3vw++;
      p2 = y3vw*y3vw;
      p2 = p2*p2+p2;
  }
}