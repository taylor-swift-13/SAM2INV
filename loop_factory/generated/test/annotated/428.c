int main1(int i){
  int g5, o3y, f;
  g5=i+17;
  o3y=g5;
  f=g5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f >= i + 17;
  loop invariant g5 == \at(i,Pre) + 17;
  loop invariant o3y + 2*f == 3 * (\at(i,Pre) + 17);
  loop invariant f >= \at(i,Pre) + 17;
  loop assigns f, o3y;
*/
while (1) {
      if (!(o3y>=2)) {
          break;
      }
      f = f + 1;
      o3y -= 2;
  }
}