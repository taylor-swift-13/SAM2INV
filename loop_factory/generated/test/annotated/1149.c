int main1(){
  int lvi, d3e7, uz, u1, yg;
  lvi=79;
  d3e7=lvi;
  uz=lvi;
  u1=3;
  yg=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lvi == 79;
  loop invariant yg >= 0;
  loop invariant d3e7 >= 0;
  loop invariant yg <= 9;
  loop invariant u1 >= 3;
  loop invariant uz - u1 == 76;
  loop assigns d3e7, uz, u1, yg;
*/
while (yg>0) {
      d3e7 = d3e7+uz*uz;
      u1 = (yg*yg)+(u1);
      uz = uz+yg*yg;
      d3e7 = d3e7*4;
      yg = yg - 1;
  }
}