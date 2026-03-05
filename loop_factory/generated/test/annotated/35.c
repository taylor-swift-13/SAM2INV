int main1(int q,int d){
  int yh;
  yh=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yh == -2 || yh == 0;
  loop invariant d == \at(d, Pre);
  loop assigns q, yh;
*/
while (yh!=0&&yh!=0) {
      if (yh>yh) {
          yh = yh - yh;
      }
      else {
          yh = yh - yh;
      }
      q = q + yh;
      q += 1;
  }
}