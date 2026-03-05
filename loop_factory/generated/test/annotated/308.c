int main1(){
  int cg, tn, vn9;
  cg=(1%18)+12;
  tn=3;
  vn9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vn9 == 0;
  loop invariant cg == 13;
  loop invariant 3 <= tn <= cg;
  loop assigns tn, vn9;
*/
while (tn<cg) {
      if (vn9==0) {
          vn9 = vn9 + 1;
          vn9--;
          vn9 = 1;
      }
      else {
          vn9--;
          vn9 = vn9 + 1;
          vn9 = 0;
      }
      tn++;
      vn9 = vn9 - vn9;
  }
}