int main1(int d,int h){
  int m4, n7, ep, cl, yo;
  m4=h*5;
  n7=2;
  ep=0;
  cl=n7;
  yo=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ep <= m4/2) ==> (cl == 2);
  loop invariant ep >= 0;
  loop invariant (cl - 2) % 4 == 0;
  loop invariant cl <= 2 + 4*ep;
  loop invariant cl >= 2;
  loop assigns cl, ep, yo;
*/
while (ep<m4) {
      if (!(!(ep>=m4/2))) {
          cl += 4;
      }
      ep = ep + 1;
      yo = yo+cl-ep;
  }
}