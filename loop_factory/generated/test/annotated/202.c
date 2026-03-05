int main1(int u){
  int qwe, uw8;
  qwe=3;
  uw8=qwe;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qwe == 3;
  loop invariant uw8 >= 0;
  loop invariant u >= \at(u, Pre);
  loop invariant uw8 <= qwe;
  loop assigns uw8, u;
*/
while (uw8!=0&&uw8!=0) {
      if (uw8>uw8) {
          uw8 -= uw8;
      }
      else {
          uw8 -= uw8;
      }
      u = u + qwe;
  }
}