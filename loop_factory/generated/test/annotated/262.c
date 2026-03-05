int main1(int s){
  int e3, i8, yt;
  e3=s-5;
  i8=e3;
  yt=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e3 == \at(s, Pre) - 5;
  loop invariant i8 <= e3;
  loop invariant s == \at(s, Pre);
  loop invariant yt - 2 == 2*(i8 - e3);
  loop invariant yt >= 2;
  loop assigns i8, yt;
*/
while (i8<e3) {
      yt += 2;
      i8 += 1;
  }
}