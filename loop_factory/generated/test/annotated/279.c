int main1(int t){
  int m4pv, q8, yh;
  m4pv=30;
  q8=m4pv;
  yh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m4pv == 30;
  loop invariant q8 >= 30;
  loop invariant t == \at(t, Pre);
  loop invariant yh == 0 || yh == 1;
  loop invariant (yh == 0) ==> (q8 == 30);
  loop assigns yh, q8;
*/
while (yh>0&&yh<=m4pv) {
      if (yh>yh) {
          yh = yh - yh;
      }
      else {
          yh = 0;
      }
      yh = yh + 1;
      q8++;
  }
}